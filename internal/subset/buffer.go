package subset

import (
	"go/types"
	"maps"
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

func receiverSliceIndex(addr ssa.Value, receiver *ssa.Parameter) *ssa.IndexAddr {
	index, _ := recordAddressBase(addr).(*ssa.IndexAddr)
	if index != nil && fieldLoad(index.X, receiver) != nil && Type(index.X.Type()).SliceElem() != "" {
		return index
	}
	return nil
}

func (m *StatefulMethod) bufferIndex(addr ssa.Value) *ssa.IndexAddr {
	index := receiverSliceIndex(addr, m.Receiver)
	if index != nil && m.Buffers[fieldLoad(index.X, m.Receiver).Field] {
		return index
	}
	return nil
}

func (m *StatefulMethod) bufferWriteField(store *ssa.Store) *ssa.FieldAddr {
	if field := sameReceiverField(store.Addr, m.Receiver); field != nil && m.Buffers[field.Field] {
		return field
	}
	if index := m.bufferIndex(store.Addr); index != nil {
		return fieldLoad(index.X, m.Receiver)
	}
	return nil
}

func bufferAllocation(value ssa.Value) bool {
	switch value := value.(type) {
	case *ssa.MakeSlice:
		return true
	case *ssa.Slice:
		_, ok := FixedSliceAllocation(value)
		return ok
	default:
		return false
	}
}

// Layout is shared by all checked transitions on the same receiver type.
// Discover it before checking any root, including through private helpers.
func findReceiverBuffers(roots []*ssa.Function) map[*types.Named]map[int]bool {
	buffers := make(map[*types.Named]map[int]bool)
	seen := make(map[*ssa.Function]bool)
	var visit func(*ssa.Function)
	visit = func(fn *ssa.Function) {
		receiver := pointerReceiver(fn)
		if receiver == nil || seen[fn] {
			return
		}
		seen[fn] = true
		record := StatefulRecord(receiver.Type())
		if record == nil {
			return
		}
		for _, block := range fn.Blocks {
			for _, ins := range block.Instrs {
				switch ins := ins.(type) {
				case *ssa.Store:
					field := sameReceiverField(ins.Addr, receiver)
					if index := receiverSliceIndex(ins.Addr, receiver); index != nil {
						field = fieldLoad(index.X, receiver)
					} else if appendCall, ok := ins.Val.(*ssa.Call); !bufferAllocation(ins.Val) && (!ok || !builtinNamed(appendCall, "append")) {
						continue
					}
					if field != nil && Type(record.Underlying().(*types.Struct).Field(field.Field).Type()).SliceElem() != "" {
						if buffers[record] == nil {
							buffers[record] = make(map[int]bool)
						}
						buffers[record][field.Field] = true
					}
				case *ssa.Call:
					if len(ins.Call.Args) > 0 && ins.Call.Args[0] == receiver {
						visit(ins.Call.StaticCallee())
					}
				}
			}
		}
	}
	for _, root := range roots {
		visit(root)
	}
	return buffers
}

// No values stored in buffers or sent to command helpers carry aliases.
func bufferValue(t types.Type) bool {
	if record, ok := t.Underlying().(*types.Struct); ok {
		for field := range record.Fields() {
			if !bufferValue(field.Type()) {
				return false
			}
		}
		return Type(t).IsRecord()
	}
	typ := Type(t)
	return typ.IsInteger() || typ == ir.Bool
}

func (c *checker) containsBufferRecord(t types.Type) bool {
	if len(c.bufferFields) == 0 {
		return false
	}
	seen := make(map[types.Type]bool)
	var visit func(types.Type) bool
	visit = func(t types.Type) bool {
		t = types.Unalias(t)
		if seen[t] {
			return false
		}
		seen[t] = true
		if named, ok := t.(*types.Named); ok && len(c.bufferFields[named]) != 0 {
			return true
		}
		switch shape := t.Underlying().(type) {
		case *types.Pointer:
			return visit(shape.Elem())
		case *types.Slice:
			return visit(shape.Elem())
		case *types.Array:
			return visit(shape.Elem())
		case *types.Struct:
			for field := range shape.Fields() {
				if visit(field.Type()) {
					return true
				}
			}
		case *types.Tuple:
			for field := range shape.Variables() {
				if visit(field.Type()) {
					return true
				}
			}
		}
		return false
	}
	return visit(t)
}

func (c *checker) checkOrdinaryBufferRecords(fn *ssa.Function) error {
	if len(c.bufferFields) == 0 {
		return nil
	}
	const message = "owned buffer records may only be used as tracked pointer receivers"
	for _, param := range fn.Params {
		if c.containsBufferRecord(param.Type()) {
			return diagnostic(fn, param.Pos(), message)
		}
	}
	if c.containsBufferRecord(fn.Signature.Results()) {
		return diagnostic(fn, fn.Pos(), message)
	}
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			if value, ok := ins.(ssa.Value); ok && c.containsBufferRecord(value.Type()) {
				return diagnostic(fn, ins.Pos(), message)
			}
		}
	}
	return nil
}

func bufferCommand(caller, callee *ssa.Function, args []ssa.Value) bool {
	if callee == nil || callee.Pkg != caller.Pkg || callee.Signature.Recv() != nil ||
		callee.Signature.Results().Len() == 0 {
		return false
	}
	for _, arg := range args {
		if !bufferValue(arg.Type()) {
			return false
		}
	}
	for result := range callee.Signature.Results().Variables() {
		if !bufferValue(result.Type()) {
			return false
		}
	}
	return true
}

func (c *checker) checkBufferUses(fn *ssa.Function, method *StatefulMethod) error {
	if len(method.Buffers) == 0 {
		return nil
	}
	receiver := method.Receiver
	for _, block := range fn.Blocks {
		for index, ins := range block.Instrs {
			switch ins := ins.(type) {
			case *ssa.Call:
				if !builtinNamed(ins, "append") || len(ins.Call.Args) != 2 {
					continue
				}
				field := fieldLoad(ins.Call.Args[0], receiver)
				if field == nil || !method.Buffers[field.Field] {
					continue
				}
				element, packaging := singleAppendArgument(ins, index)
				store, ok := bufferStore(ins, receiver)
				if element == nil || !bufferValue(element.Type()) || !ok || store.Field != field.Field ||
					!bufferUseIsLocal(ins, (*ins.Referrers())[0], method) {
					return diagnostic(fn, ins.Pos(), "owned buffer append requires one value element and a direct store back to the same field")
				}
				c.collectionAppends[ins] = element
				for _, temp := range packaging {
					c.collectionPackaging[temp] = true
				}
			case *ssa.MakeSlice, *ssa.Slice:
				value := ins.(ssa.Value)
				if !bufferAllocation(value) {
					continue
				}
				store, ok := bufferStore(value, receiver)
				element := value.Type().Underlying().(*types.Slice).Elem()
				if !ok || !method.Buffers[store.Field] || !bufferValue(element) {
					continue
				}
				c.owned[value] = value
				if fixed, ok := value.(*ssa.Slice); ok {
					c.collectionPackaging[fixed.X.(*ssa.Alloc)] = true
				}
			}
		}
	}
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			switch ins := ins.(type) {
			case *ssa.UnOp:
				if field := fieldLoad(ins, receiver); field != nil && method.Buffers[field.Field] {
					for _, use := range *ins.Referrers() {
						if !c.bufferRead(use, ins) || !bufferUseIsLocal(ins, use, method) {
							return diagnostic(fn, use.Pos(), "owned buffer slice cannot escape or be reused after a receiver update")
						}
					}
				}
			case *ssa.IndexAddr, *ssa.FieldAddr:
				addr := ins.(ssa.Value)
				if root := method.bufferIndex(addr); root != nil {
					for _, use := range *addr.Referrers() {
						if !bufferAddressUse(use, addr) || !bufferUseIsLocal(root, use, method) {
							return diagnostic(fn, use.Pos(), "owned buffer element address must stay local and cannot outlive a receiver update")
						}
					}
				}
			case *ssa.Store:
				field := sameReceiverField(ins.Addr, receiver)
				if field == nil || !method.Buffers[field.Field] {
					continue
				}
				appendCall, _ := ins.Val.(*ssa.Call)
				if c.owned[ins.Val] == nil && c.collectionAppends[appendCall] == nil {
					return diagnostic(fn, ins.Pos(), "owned buffer field requires a fresh allocation or an append to that same field")
				}
			}
		}
	}
	return nil
}

func bufferStore(value ssa.Value, receiver *ssa.Parameter) (*ssa.FieldAddr, bool) {
	if len(*value.Referrers()) != 1 {
		return nil, false
	}
	store, ok := (*value.Referrers())[0].(*ssa.Store)
	if !ok || store.Val != value || store.Block() != value.(ssa.Instruction).Block() {
		return nil, false
	}
	field := sameReceiverField(store.Addr, receiver)
	return field, field != nil
}

func (c *checker) bufferRead(use ssa.Instruction, load *ssa.UnOp) bool {
	switch use := use.(type) {
	case *ssa.IndexAddr:
		return use.X == load && use.Index != load
	case *ssa.Call:
		return len(use.Call.Args) > 0 && use.Call.Args[0] == load && (IsLength(use) || c.collectionAppends[use] != nil)
	default:
		return false
	}
}

func bufferAddressUse(use ssa.Instruction, addr ssa.Value) bool {
	switch use := use.(type) {
	case *ssa.FieldAddr:
		return use.X == addr
	case *ssa.Store:
		return use.Addr == addr && use.Val != addr
	default:
		return readsCell(use, addr)
	}
}

func bufferUseIsLocal(first, last ssa.Instruction, method *StatefulMethod) bool {
	if first.Block() != last.Block() {
		return false
	}
	steps := first.Block().Instrs
	start, end := slices.Index(steps, first), slices.Index(steps, last)
	if start >= end {
		return false
	}
	for _, ins := range steps[start+1 : end] {
		switch ins := ins.(type) {
		case *ssa.Store:
			if method.bufferWriteField(ins) != nil {
				return false
			}
		case *ssa.Call:
			if slices.Contains(ins.Call.Args, ssa.Value(method.Receiver)) {
				return false
			}
		}
	}
	return true
}

// The root receives a Go receiver from outside the checked call graph. Its
// slices may share backing arrays, so every mutable buffer needs a fresh
// allocation before its first write, including through receiver helpers.
func (c *checker) checkBufferEntry(fn *ssa.Function) error {
	if len(c.stateful[fn].Buffers) == 0 {
		return nil
	}
	_, err := c.bufferExit(fn, nil)
	return err
}

func (c *checker) bufferExit(fn *ssa.Function, entry map[int]bool) (map[int]bool, error) {
	method := c.stateful[fn]
	pending := []*ssa.BasicBlock{fn.Blocks[0]}
	inputs := map[*ssa.BasicBlock]map[int]bool{fn.Blocks[0]: entry}
	var exit map[int]bool
	returned := false
	for len(pending) > 0 {
		block := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		owned := make(map[int]bool)
		maps.Copy(owned, inputs[block])
		for _, ins := range block.Instrs {
			switch ins := ins.(type) {
			case *ssa.Store:
				field := method.bufferWriteField(ins)
				if field == nil {
					continue
				}
				if c.owned[ins.Val] != nil {
					owned[field.Field] = true
				} else if !owned[field.Field] {
					return nil, diagnostic(fn, ins.Pos(), "owned buffer must be freshly initialized before mutation")
				}
			case *ssa.Call:
				callee := ins.Call.StaticCallee()
				if c.stateful[callee] == nil {
					continue
				}
				var err error
				owned, err = c.bufferExit(callee, owned)
				if err != nil {
					return nil, err
				}
			case *ssa.Return:
				if !returned {
					exit, returned = owned, true
				} else {
					intersectBuffers(exit, owned)
				}
			}
		}
		for _, successor := range block.Succs {
			if previous, ok := inputs[successor]; !ok {
				inputs[successor] = maps.Clone(owned)
			} else if !intersectBuffers(previous, owned) {
				continue
			}
			pending = append(pending, successor)
		}
	}
	return exit, nil
}

func intersectBuffers(previous, incoming map[int]bool) bool {
	before := len(previous)
	for field := range previous {
		if !incoming[field] {
			delete(previous, field)
		}
	}
	return len(previous) != before
}
