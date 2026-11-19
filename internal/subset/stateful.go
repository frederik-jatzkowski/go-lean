package subset

import (
	"go/constant"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

// StatefulMethod describes the checked boundary of a receiver-state transition.
type StatefulMethod struct {
	Receiver *ssa.Parameter
	Callback *ssa.Parameter
	Loop     *IndexedLoop
	writes   map[int]bool
}

type IndexedLoop struct {
	Header   *ssa.BasicBlock
	Sequence *ssa.FieldAddr
	Cursor   *ssa.FieldAddr
}

func StatefulRecord(t types.Type) *types.Named {
	pointer, ok := types.Unalias(t).(*types.Pointer)
	if !ok {
		return nil
	}
	named, ok := types.Unalias(pointer.Elem()).(*types.Named)
	if !ok || named.TypeParams().Len() != 0 || named.Obj().Pkg() == nil {
		return nil
	}
	record, ok := named.Underlying().(*types.Struct)
	if !ok {
		return nil
	}
	for field := range record.Fields() {
		if field.Name() == "_" || !stateValueType(field.Type()) {
			return nil
		}
	}
	return named
}

func stateValueType(t types.Type) bool {
	typ := Type(t)
	return typ.IsInteger() || typ == ir.Bool || typ.IsRecord() || typ.SliceElem().IsRecord() ||
		typ.SliceElem().IsInteger() || typ.SliceElem() == ir.Bool
}

func stateValue(value ssa.Value) bool {
	return stateValueType(value.Type()) && supportedValue(value)
}

func pointerReceiver(fn *ssa.Function) *ssa.Parameter {
	if fn == nil || fn.Signature.Recv() == nil || len(fn.Params) == 0 {
		return nil
	}
	if _, ok := types.Unalias(fn.Params[0].Type()).(*types.Pointer); !ok {
		return nil
	}
	return fn.Params[0]
}

func writesReceiver(fn *ssa.Function, seen map[*ssa.Function]bool) bool {
	receiver := pointerReceiver(fn)
	if receiver == nil || seen[fn] {
		return false
	}
	seen[fn] = true
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			switch ins := ins.(type) {
			case *ssa.Store:
				if recordAddressBase(ins.Addr) == receiver {
					return true
				}
			case *ssa.Call:
				if len(ins.Call.Args) > 0 && ins.Call.Args[0] == receiver &&
					writesReceiver(ins.Call.StaticCallee(), seen) {
					return true
				}
			}
		}
	}
	return false
}

func (c *checker) checkStateful(fn *ssa.Function) error {
	if c.stateful[fn] != nil {
		return nil
	}
	if c.visiting[fn] || c.done[fn] {
		return diagnostic(fn, fn.Pos(), "stateful methods require a nonrecursive receiver call graph")
	}
	receiver := pointerReceiver(fn)
	sig := fn.Signature
	if receiver == nil || StatefulRecord(receiver.Type()) == nil || fn.Pkg == nil ||
		fn.Synthetic != "" || sig.RecvTypeParams().Len() != 0 || sig.Variadic() || len(fn.Blocks) == 0 ||
		sig.Results().Len() > 1 || sig.Results().Len() == 1 && !stateValueType(sig.Results().At(0).Type()) {
		return diagnostic(fn, fn.Pos(), "stateful methods require a declared record pointer receiver and at most one supported result")
	}
	spec := &StatefulMethod{Receiver: receiver, writes: make(map[int]bool)}
	for _, param := range fn.Params[1:] {
		if stateValueType(param.Type()) {
			continue
		}
		if spec.Callback == nil && BooleanCallbackInput(param.Type()) != nil {
			spec.Callback = param
			continue
		}
		return diagnostic(fn, param.Pos(), "unsupported stateful method parameter")
	}
	c.visiting[fn] = true
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			if !c.stateInstruction(fn, spec, ins) {
				return diagnostic(fn, ins.Pos(), "unsupported receiver-state instruction or operand: %s", ins)
			}
			switch ins := ins.(type) {
			case *ssa.Store:
				if field := sameReceiverField(ins.Addr, receiver); field != nil {
					spec.writes[field.Field] = true
				}
			case *ssa.Call:
				if callee := c.stateful[ins.Call.StaticCallee()]; callee != nil {
					for field := range callee.writes {
						spec.writes[field] = true
					}
				}
			}
		}
	}
	if err := checkAcyclic(fn); err != nil {
		spec.Loop = c.indexedLoop(fn, receiver)
		if spec.Loop == nil {
			return diagnostic(fn, fn.Pos(), "stateful loops require a slice-length bound and one cursor increment on every back edge")
		}
	}
	delete(c.visiting, fn)
	c.stateful[fn] = spec
	c.ordered = append(c.ordered, fn)
	return nil
}

func BooleanCallbackInput(t types.Type) types.Type {
	sig, ok := types.Unalias(t).(*types.Signature)
	if !ok || sig.Variadic() || sig.Params().Len() != 1 || sig.Results().Len() != 1 ||
		!types.Identical(sig.Results().At(0).Type(), types.Typ[types.Bool]) {
		return nil
	}
	input := sig.Params().At(0).Type()
	if Type(input).IsInteger() || Type(input) == ir.Bool {
		return input
	}
	return nil
}

func IsSliceClone(call *ssa.Call) bool {
	target := call.Call.StaticCallee()
	if target == nil || target.Origin() == nil || len(call.Call.Args) != 1 {
		return false
	}
	origin := target.Origin()
	return origin.Pkg != nil && origin.Pkg.Pkg.Path() == "slices" && origin.Name() == "Clone" &&
		Type(call.Type()).SliceElem() != "" && types.Identical(call.Type(), call.Call.Args[0].Type())
}

func sameReceiverField(value ssa.Value, receiver *ssa.Parameter) *ssa.FieldAddr {
	if addr, ok := value.(*ssa.FieldAddr); ok && addr.X == receiver {
		return addr
	}
	return nil
}

func fieldLoad(value ssa.Value, receiver *ssa.Parameter) *ssa.FieldAddr {
	if load, ok := value.(*ssa.UnOp); ok && load.Op == token.MUL {
		return sameReceiverField(load.X, receiver)
	}
	return nil
}

func (c *checker) stateInstruction(fn *ssa.Function, spec *StatefulMethod, ins ssa.Instruction) bool {
	receiver := spec.Receiver
	switch ins := ins.(type) {
	case *ssa.Alloc:
		if !ins.Heap && CaptureType(ins.Type()).IsRecord() {
			if cell, ok := recordInitializer(ins); ok {
				c.records[ins] = cell
				return true
			}
		}
	case *ssa.FieldAddr:
		if sameReceiverField(ins, receiver) != nil {
			for _, use := range *ins.Referrers() {
				if store, ok := use.(*ssa.Store); (!ok || store.Addr != ins) && !readsCell(use, ins) {
					return false
				}
			}
			return true
		}
		return c.isRecordAddress(ins)
	case *ssa.IndexAddr:
		if !stateValue(ins.X) || Type(ins.X.Type()).SliceElem() == "" || !supportedIndex(ins.Index) {
			return false
		}
		for _, use := range *ins.Referrers() {
			if !readsCell(use, ins) {
				return false
			}
		}
		return true
	case *ssa.UnOp:
		if ins.Op == token.MUL {
			_, indexed := ins.X.(*ssa.IndexAddr)
			return stateValue(ins) && (indexed || sameReceiverField(ins.X, receiver) != nil || c.isRecordAddress(ins.X))
		}
		return stateValue(ins.X) && c.instruction(fn, ins) == nil
	case *ssa.Store:
		return stateValue(ins.Val) && (sameReceiverField(ins.Addr, receiver) != nil || c.isRecordAddress(ins.Addr))
	case *ssa.Call:
		args := ins.Call.Args
		if len(args) == 1 && (IsLength(ins) || IsSliceClone(ins)) {
			return stateValue(args[0]) && Type(args[0].Type()).SliceElem() != ""
		}
		if spec.Callback != nil && ins.Call.Value == spec.Callback {
			return len(args) == 1 && stateValue(args[0])
		}
		target := ins.Call.StaticCallee()
		if target == nil || len(args) == 0 || args[0] != receiver || pointerReceiver(target) == nil ||
			!types.Identical(receiver.Type(), target.Params[0].Type()) {
			return false
		}
		for _, arg := range args[1:] {
			if !stateValue(arg) {
				return false
			}
		}
		return c.checkStateful(target) == nil && c.stateful[target].Callback == nil
	case *ssa.Return:
		return len(ins.Results) == 0 || len(ins.Results) == 1 && stateValue(ins.Results[0])
	case *ssa.BinOp:
		return stateValue(ins.X) && stateValue(ins.Y) && c.instruction(fn, ins) == nil
	case *ssa.Convert:
		return stateValue(ins.X) && stateValue(ins) && c.instruction(fn, ins) == nil
	case *ssa.ChangeType:
		return stateValue(ins.X) && stateValue(ins) && c.instruction(fn, ins) == nil
	case *ssa.Field, *ssa.If, *ssa.Jump:
		return c.instruction(fn, ins) == nil
	case *ssa.Phi:
		for _, edge := range ins.Edges {
			if !stateValue(edge) {
				return false
			}
		}
		return c.instruction(fn, ins) == nil
	}
	return false
}

func (c *checker) indexedLoop(fn *ssa.Function, receiver *ssa.Parameter) *IndexedLoop {
	entry := fn.Blocks[0]
	if !endsInJump(entry) || len(entry.Succs) != 1 {
		return nil
	}
	for _, ins := range entry.Instrs[:len(entry.Instrs)-1] {
		if value, ok := ins.(ssa.Value); ok && value.Referrers() != nil {
			for _, use := range *value.Referrers() {
				if use.Block() != entry {
					return nil
				}
			}
		}
	}
	header := entry.Succs[0]
	branch, ok := header.Instrs[len(header.Instrs)-1].(*ssa.If)
	if !ok || len(header.Preds) < 2 {
		return nil
	}
	compare, ok := branch.Cond.(*ssa.BinOp)
	if !ok || compare.Op != token.LSS || Type(compare.X.Type()) != ir.IntWord {
		return nil
	}
	cursor := fieldLoad(compare.X, receiver)
	length, ok := compare.Y.(*ssa.Call)
	if cursor == nil || !ok || !IsLength(length) {
		return nil
	}
	sequence := fieldLoad(length.Call.Args[0], receiver)
	if sequence == nil ||
		compare.Block() != header || length.Block() != header ||
		cursor.Block() != header || sequence.Block() != header {
		return nil
	}
	// Restrict the header to the actual guard, without writes or loop-carried SSA values.
	for _, ins := range header.Instrs[:len(header.Instrs)-1] {
		if ins != cursor && ins != sequence && ins != compare && ins != length && ins != compare.X.(*ssa.UnOp) && ins != length.Call.Args[0].(*ssa.UnOp) {
			return nil
		}
	}
	loop := &IndexedLoop{Header: header, Sequence: sequence, Cursor: cursor}
	if !c.checkLoopPaths(loop, header.Succs[0], receiver, false, 0, map[*ssa.BasicBlock]bool{header: true}) ||
		!c.checkLoopPaths(loop, header.Succs[1], receiver, true, 0, map[*ssa.BasicBlock]bool{header: true}) {
		return nil
	}
	return loop
}

func (c *checker) checkLoopPaths(loop *IndexedLoop, block *ssa.BasicBlock, receiver *ssa.Parameter, invalid bool, increments int, active map[*ssa.BasicBlock]bool) bool {
	if block == loop.Header {
		return !invalid && increments == 1
	}
	if active[block] {
		return false
	}
	active[block] = true
	defer delete(active, block)
	for _, ins := range block.Instrs {
		switch ins := ins.(type) {
		case *ssa.Call:
			if len(ins.Call.Args) > 0 && ins.Call.Args[0] == receiver {
				callee := c.stateful[ins.Call.StaticCallee()]
				invalid = invalid || callee == nil || callee.writes[loop.Cursor.Field] || callee.writes[loop.Sequence.Field]
			}
		case *ssa.Store:
			if field := sameReceiverField(ins.Addr, receiver); field != nil {
				switch field.Field {
				case loop.Sequence.Field:
					invalid = true
				case loop.Cursor.Field:
					increments++
					add, ok := ins.Val.(*ssa.BinOp)
					if !ok || add.Op != token.ADD {
						invalid = true
						continue
					}
					load := fieldLoad(add.X, receiver)
					one, ok := add.Y.(*ssa.Const)
					if load == nil || load.Field != loop.Cursor.Field || !ok ||
						!constant.Compare(one.Value, token.EQL, constant.MakeInt64(1)) {
						invalid = true
					}
				}
			}
		}
	}
	for _, successor := range block.Succs {
		if !c.checkLoopPaths(loop, successor, receiver, invalid, increments, active) {
			return false
		}
	}
	return true
}
