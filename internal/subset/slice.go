package subset

import "golang.org/x/tools/go/ssa"

// SliceBuild captures a checked fresh slice returned after a full iteration.
type SliceBuild struct {
	Source  ssa.Value
	Element *ssa.UnOp
	Steps   []ssa.Value
	Value   ssa.Value
}

func checkSliceBuild(blocks loopBlocks) *SliceBuild {
	iter := matchRangeIteration(blocks, 1)
	dst, allocated := blocks.result.(*ssa.MakeSlice)
	if iter == nil || !allocated || dst.Block() != blocks.entry {
		return nil
	}
	dstElem := Type(dst.Type()).SliceElem()
	if dstElem == "" || dstElem != Type(iter.Source.Type()).SliceElem() ||
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
	addr, addrOK := body[end].(*ssa.IndexAddr)
	store, storeOK := body[end+1].(*ssa.Store)
	if !addrOK || !storeOK || addr.X != dst || addr.Index != iter.Index || store.Addr != addr ||
		!hasType(store.Val, dstElem) {
		return nil
	}
	// No other operation can use the result or its element address before return.
	available := map[ssa.Value]bool{iter.Element: true}
	steps, ok := pureInt64Steps(body[2:end], nil, available)
	if !ok || !loopValue(store.Val, available) {
		return nil
	}
	return &SliceBuild{Source: iter.Source, Element: iter.Element, Steps: steps, Value: store.Val}
}

func lengthOf(value, sequence ssa.Value) bool {
	call, ok := value.(*ssa.Call)
	return ok && IsLength(call) && len(call.Call.Args) == 1 && call.Call.Args[0] == sequence
}
