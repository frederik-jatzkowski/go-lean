package subset

import (
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

// SliceBuild captures a checked fresh slice returned after a full iteration.
type SliceBuild struct {
	Destination *ssa.MakeSlice
	Exit        *ssa.BasicBlock
	ExitStart   int
	Lengths     []*ssa.Call
	Copy        *ssa.Call
	Source      ssa.Value
	Element     *ssa.UnOp
	Steps       []ssa.Value
	Value       ssa.Value
	Callback    *ssa.Parameter
	Effectful   bool
	Callbacks   []*ssa.Function
	Iteration   *TraversalIteration
}

func checkSliceBuild(blocks loopBlocks) *SliceBuild {
	iter := matchRangeIteration(blocks, 1)
	dst := sliceDestination(blocks.exit)
	allocated := dst != nil
	if iter == nil || !allocated || dst.Block() != blocks.entry {
		return nil
	}
	dstElem := Type(dst.Type()).SliceElem()
	if dstElem == "" ||
		!lengthOf(dst.Len, iter.Source) || !lengthOf(dst.Cap, iter.Source) {
		return nil
	}
	// The preheader can only measure the input length and allocate this result.
	for _, ins := range blocks.entry.Instrs[:len(blocks.entry.Instrs)-1] {
		if ins == dst {
			continue
		}
		if value, ok := ins.(ssa.Value); !ok || !lengthOf(value, iter.Source) {
			return nil
		}
	}
	body := blocks.body.Instrs
	if len(body) < 5 {
		return nil
	}
	end := len(body) - 3
	if iter.LatchStep != nil {
		end--
	}
	if end < 2 {
		return nil
	}
	addr, addrOK := body[end].(*ssa.IndexAddr)
	store, storeOK := body[end+1].(*ssa.Store)
	if !addrOK || !storeOK || addr.X != dst || addr.Index != iter.Index || store.Addr != addr ||
		!hasType(store.Val, dstElem) {
		return nil
	}
	// No other operation can use the result or its element address before return.
	if end == 3 {
		if call, ok := body[2].(*ssa.Call); ok && call == store.Val && !call.Call.IsInvoke() &&
			len(call.Call.Args) == 1 && call.Call.Args[0] == iter.Element {
			if callback, ok := call.Call.Value.(*ssa.Parameter); ok &&
				callbackType(callback.Type(), Type(iter.Element.Type()), dstElem) != "" {
				return sliceContinuation(&SliceBuild{Source: iter.Source, Element: iter.Element, Steps: []ssa.Value{call}, Value: call, Callback: callback}, dst, blocks.exit, 0, nil)
			}
		}
	}
	available := map[ssa.Value]bool{iter.Element: true}
	steps, ok := pureInt64Steps(body[2:end], nil, available)
	if !ok || !loopValue(store.Val, available) {
		return nil
	}
	return sliceContinuation(&SliceBuild{Source: iter.Source, Element: iter.Element, Steps: steps, Value: store.Val}, dst, blocks.exit, 0, nil)
}

// CallbackType represents the function parameter validated by the slice build.
func (b SliceBuild) CallbackType() ir.Type {
	input, output := Type(b.Element.Type()), Type(b.Value.Type())
	if b.Effectful {
		output = ir.OptionType(output)
	}
	return ir.UnaryFunctionType(input, output)
}

func callbackType(typ types.Type, input, output ir.Type) ir.Type {
	sig, ok := types.Unalias(typ).(*types.Signature)
	if ok && !sig.Variadic() && sig.Params().Len() == 1 && sig.Results().Len() == 1 &&
		Type(sig.Params().At(0).Type()) == input && Type(sig.Results().At(0).Type()) == output {
		return ir.UnaryFunctionType(input, output)
	}
	return ""
}

func lengthOf(value, sequence ssa.Value) bool {
	call, ok := value.(*ssa.Call)
	return ok && IsLength(call) && len(call.Call.Args) == 1 && call.Call.Args[0] == sequence
}

// checkSliceCopy recognizes a full copy into an exactly sized fresh allocation.
// The copied count is unused, and neither the allocation nor its storage escapes
// before the return.
func checkSliceCopy(fn *ssa.Function) *SliceBuild {
	if len(fn.Blocks) != 1 {
		return nil
	}
	instructions := fn.Blocks[0].Instrs
	if len(instructions) < 4 {
		return nil
	}
	length, lengthOK := instructions[0].(*ssa.Call)
	dst, dstOK := instructions[1].(*ssa.MakeSlice)
	copyCall, copyOK := instructions[2].(*ssa.Call)
	if !lengthOK || !dstOK || !copyOK || sliceDestination(fn.Blocks[0]) != dst ||
		dst.Len != length || dst.Cap != length {
		return nil
	}
	builtin, ok := copyCall.Call.Value.(*ssa.Builtin)
	args := copyCall.Call.Args
	if !ok || builtin.Name() != "copy" || len(args) != 2 || args[0] != dst ||
		!lengthOf(length, args[1]) {
		return nil
	}
	src, ok := args[1].(*ssa.Parameter)
	elem := Type(dst.Type()).SliceElem()
	if !ok || elem == "" || elem != Type(src.Type()).SliceElem() {
		return nil
	}
	return sliceContinuation(&SliceBuild{Source: src}, dst, fn.Blocks[0], 3, copyCall)
}

// sliceDestination selects the one allocation modeled by the slice traversal.
func sliceDestination(block *ssa.BasicBlock) *ssa.MakeSlice {
	ret, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Return)
	if !ok {
		return nil
	}
	var destination *ssa.MakeSlice
	for _, value := range ret.Results {
		if allocation, ok := value.(*ssa.MakeSlice); ok {
			if destination != nil {
				return nil
			}
			destination = allocation
		}
	}
	return destination
}

func sliceContinuation(build *SliceBuild, dst *ssa.MakeSlice, exit *ssa.BasicBlock, start int, copyCall *ssa.Call) *SliceBuild {
	ret := exit.Instrs[len(exit.Instrs)-1].(*ssa.Return)
	if len(ret.Results) == 1 {
		if len(exit.Instrs) != start+1 {
			return nil
		}
		return build
	}
	available := make(map[ssa.Value]bool)
	setup := dst.Block().Instrs
	if dst.Block() == exit {
		setup = setup[:start]
	}
	for _, ins := range setup {
		if length, ok := ins.(*ssa.Call); ok && lengthOf(length, build.Source) {
			available[length] = true
			build.Lengths = append(build.Lengths, length)
		}
	}
	if copyCall != nil {
		available[copyCall] = true
	}
	for _, ins := range exit.Instrs[start:] {
		for _, operand := range ins.Operands(nil) {
			if operand == nil || *operand == nil || available[*operand] {
				continue
			}
			if *operand == dst && ins == ret {
				continue
			}
			switch (*operand).(type) {
			case *ssa.Const, *ssa.Parameter, *ssa.FreeVar, *ssa.Function, *ssa.Builtin:
				continue
			}
			return nil
		}
		if value, ok := ins.(ssa.Value); ok {
			available[value] = true
		}
	}
	build.Destination, build.Exit, build.ExitStart, build.Copy = dst, exit, start, copyCall
	return build
}

func sliceCallbackUse(call *ssa.Call, closure *ssa.MakeClosure) bool {
	callee := call.Call.StaticCallee()
	if callee == nil || len(callee.TypeArgs()) == 0 {
		return false
	}
	blocks, ok := matchLoopBlocks(callee)
	if !ok {
		return false
	}
	build := checkSliceBuild(blocks)
	if build == nil || build.Callback == nil {
		return false
	}
	for i, arg := range call.Call.Args {
		if arg == closure && callee.Params[i] != build.Callback {
			return false
		}
	}
	return true
}

// TraversalIteration describes the part of a checked iteration that computes a
// destination element. The bounds-proven indexing and the final store are
// represented by the traversal itself.
type TraversalIteration struct {
	Entry, Header *ssa.BasicBlock
	Skip          map[ssa.Instruction]bool
	Stores        map[ssa.Instruction]ssa.Value
}

func matchSliceIteration(fn *ssa.Function) *SliceBuild {
	blocks, ok := matchLoopRegion(fn)
	if !ok {
		return nil
	}
	iter := matchRangeIteration(blocks, 1)
	dst := sliceDestination(blocks.exit)
	if iter == nil || dst == nil || dst.Block() != blocks.entry || Type(dst.Type()).SliceElem() == "" ||
		!lengthOf(dst.Len, iter.Source) || !lengthOf(dst.Cap, iter.Source) {
		return nil
	}
	skip := map[ssa.Instruction]bool{iter.Element: true, iter.Element.X.(*ssa.IndexAddr): true}
	omitted := map[ssa.Value]bool{iter.Counter: true, iter.Index: true, dst: true, iter.Element.X: true}
	if iter.LatchStep != nil {
		skip[iter.LatchStep] = true
		omitted[iter.LatchStep] = true
	}
	for _, ins := range blocks.entry.Instrs[:len(blocks.entry.Instrs)-1] {
		if ins == dst {
			continue
		}
		length, ok := ins.(*ssa.Call)
		if !ok || !lengthOf(length, iter.Source) {
			return nil
		}
		omitted[length] = true
	}
	omitted[iter.Length] = true
	stores := make(map[ssa.Instruction]ssa.Value)
	for _, use := range *dst.Referrers() {
		if ret, ok := use.(*ssa.Return); ok && ret.Block() == blocks.exit {
			continue
		}
		addr, ok := use.(*ssa.IndexAddr)
		if !ok || addr.X != dst || addr.Index != iter.Index || addr.Block() == blocks.header {
			return nil
		}
		skip[addr], omitted[addr] = true, true
		for _, use := range *addr.Referrers() {
			store, ok := use.(*ssa.Store)
			if !ok || store.Addr != addr || !hasType(store.Val, Type(dst.Type()).SliceElem()) {
				return nil
			}
			stores[store], skip[store] = store.Val, true
		}
	}
	if !writesOncePerIteration(blocks.body, blocks.header, stores) {
		return nil
	}
	for _, value := range stores {
		if omitted[value] {
			return nil
		}
	}
	for _, block := range fn.Blocks {
		if block == blocks.entry || block == blocks.header || block == blocks.exit {
			continue
		}
		for _, ins := range block.Instrs {
			if skip[ins] {
				continue
			}
			if !iterationInstruction(ins) {
				return nil
			}
			for _, operand := range ins.Operands(nil) {
				if operand != nil && omitted[*operand] {
					return nil
				}
			}
		}
	}
	return sliceContinuation(&SliceBuild{Source: iter.Source, Element: iter.Element,
		Iteration: &TraversalIteration{Entry: blocks.body, Header: blocks.header, Skip: skip, Stores: stores}}, dst, blocks.exit, 0, nil)
}

// The loop region is already known to be acyclic up to its header. Validate
// the write count at each back edge, including paths that join before it.
func writesOncePerIteration(body, header *ssa.BasicBlock, stores map[ssa.Instruction]ssa.Value) bool {
	type path struct {
		block  *ssa.BasicBlock
		writes int
	}
	seen := make(map[path]bool)
	var visit func(*ssa.BasicBlock, int) bool
	visit = func(block *ssa.BasicBlock, writes int) bool {
		if block == header {
			return writes == 1
		}
		key := path{block, writes}
		if seen[key] {
			return true
		}
		seen[key] = true
		for _, ins := range block.Instrs {
			if stores[ins] != nil {
				writes++
			}
		}
		if writes > 1 {
			return false
		}
		for _, successor := range block.Succs {
			if !visit(successor, writes) {
				return false
			}
		}
		return true
	}
	return visit(body, 0)
}

func iterationInstruction(ins ssa.Instruction) bool {
	switch ins.(type) {
	case *ssa.BinOp, *ssa.UnOp, *ssa.Convert, *ssa.ChangeType, *ssa.Call, *ssa.Field,
		*ssa.If, *ssa.Jump, *ssa.Phi, *ssa.Extract:
		return true
	default:
		return false
	}
}

func (c *checker) checkIteration(fn *ssa.Function, iter *TraversalIteration) error {
	for _, block := range fn.Blocks {
		if block == fn.Blocks[0] || block == iter.Header || block == iter.Header.Succs[1] {
			continue
		}
		for _, ins := range block.Instrs {
			if iter.Skip[ins] {
				continue
			}
			if err := c.instruction(fn, ins); err != nil {
				return err
			}
		}
	}
	return nil
}
