package subset

import (
	"go/constant"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

// matchCollectionFold consumes the entire function. The only uses of the two
// allocations are the checked loop operations and the final return.
func matchCollectionFold(fn *ssa.Function) *RangeFold {
	blocks, ok := matchLoopRegion(fn)
	if !ok || len(fn.Blocks) != 5 || len(blocks.entry.Instrs) != 5 ||
		len(blocks.body.Instrs) != 4 || len(blocks.exit.Instrs) != 1 ||
		len(blocks.backs) != 2 {
		return nil
	}
	iter := matchRangeIteration(blocks, 2)
	if iter == nil || Type(iter.Source.Type()) != ir.SliceType(ir.Bytes) ||
		iter.Length != blocks.entry.Instrs[3] {
		return nil
	}
	capacity, ok := blocks.entry.Instrs[0].(*ssa.Call)
	if !ok || !IsLength(capacity) || len(capacity.Call.Args) != 1 || capacity.Call.Args[0] != iter.Source {
		return nil
	}
	dst, ok := blocks.entry.Instrs[1].(*ssa.MakeSlice)
	if !ok || dst.Cap != capacity || !IsZero(dst.Len) || Type(dst.Type()) != Type(iter.Source.Type()) {
		return nil
	}
	counts, ok := blocks.entry.Instrs[2].(*ssa.MakeMap)
	if !ok || counts.Reserve != nil || Type(counts.Type()) != ir.MapType(ir.Bytes, ir.IntWord) {
		return nil
	}
	condition, ok := blocks.body.Instrs[2].(*ssa.BinOp)
	if !ok || condition.Op != token.EQL || condition.X != iter.Element {
		return nil
	}
	excluded, ok := condition.Y.(*ssa.Const)
	if !ok || excluded.Value == nil || excluded.Value.Kind() != constant.String {
		return nil
	}
	branch, ok := blocks.body.Instrs[3].(*ssa.If)
	if !ok || branch.Cond != condition || blocks.body.Succs[0] != blocks.header {
		return nil
	}
	update := blocks.body.Succs[1]
	if len(update.Instrs) != 9 || len(update.Preds) != 1 || update.Preds[0] != blocks.body ||
		len(update.Succs) != 1 || update.Succs[0] != blocks.header || !endsInJump(update) {
		return nil
	}
	ret := blocks.exit.Instrs[0].(*ssa.Return)
	if len(ret.Results) != 2 || ret.Results[1] != counts {
		return nil
	}
	state, ok := ret.Results[0].(*ssa.Phi)
	if !ok || state.Block() != blocks.header || state == iter.Counter || state.Edges[blocks.incoming] != dst {
		return nil
	}
	appendCall := matchSingleAppend(update.Instrs[:5], state, iter.Element)
	if appendCall == nil {
		return nil
	}
	for _, back := range blocks.backs {
		pred := blocks.header.Preds[back]
		if pred == blocks.body && state.Edges[back] == state ||
			pred == update && state.Edges[back] == appendCall {
			continue
		}
		return nil
	}
	lookup, ok := update.Instrs[5].(*ssa.Lookup)
	if !ok || lookup.CommaOk || lookup.X != counts || lookup.Index != iter.Element {
		return nil
	}
	next, ok := update.Instrs[6].(*ssa.BinOp)
	if !ok || next.Op != token.ADD || next.X != lookup || !intConstant(next.Y, 1) {
		return nil
	}
	write, ok := update.Instrs[7].(*ssa.MapUpdate)
	if !ok || write.Map != counts || write.Key != iter.Element || write.Value != next {
		return nil
	}
	return &RangeFold{Source: iter.Source, Excluded: excluded}
}

func matchSingleAppend(steps []ssa.Instruction, dst, element ssa.Value) *ssa.Call {
	// SSA packs one variadic argument in a temporary one-element array.
	tmp, tmpOK := steps[0].(*ssa.Alloc)
	addr, addrOK := steps[1].(*ssa.IndexAddr)
	store, storeOK := steps[2].(*ssa.Store)
	packed, packedOK := steps[3].(*ssa.Slice)
	call, callOK := steps[4].(*ssa.Call)
	if !tmpOK || !addrOK || !storeOK || !packedOK || !callOK ||
		addr.X != tmp || !IsZero(addr.Index) || store.Addr != addr || store.Val != element ||
		packed.X != tmp || packed.Low != nil || packed.High != nil || packed.Max != nil ||
		len(call.Call.Args) != 2 || call.Call.Args[0] != dst || call.Call.Args[1] != packed {
		return nil
	}
	array, ok := tmp.Type().Underlying().(*types.Pointer).Elem().Underlying().(*types.Array)
	if !ok || array.Len() != 1 || !types.Identical(array.Elem(), element.Type()) {
		return nil
	}
	builtin, ok := call.Call.Value.(*ssa.Builtin)
	if !ok || builtin.Name() != "append" {
		return nil
	}
	return call
}

func IsStringSliceCapacity(call *ssa.Call) bool {
	builtin, ok := call.Call.Value.(*ssa.Builtin)
	return ok && builtin.Name() == "cap" && len(call.Call.Args) == 1 &&
		hasType(call.Call.Args[0], ir.SliceType(ir.Bytes))
}
