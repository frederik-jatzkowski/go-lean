package subset

import (
	"go/constant"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

func arrayHasIndexedStore(cell *ssa.Alloc) bool {
	for _, use := range *cell.Referrers() {
		if address, ok := use.(*ssa.IndexAddr); ok {
			for _, access := range *address.Referrers() {
				if store, ok := access.(*ssa.Store); ok && store.Addr == address {
					return true
				}
			}
		}
	}
	return false
}

func arrayType(t types.Type) *types.Array {
	if pointer, ok := t.Underlying().(*types.Pointer); ok {
		t = pointer.Elem()
	}
	array, _ := t.Underlying().(*types.Array)
	return array
}

func concreteArrayElement(array *types.Array) bool {
	_, generic := types.Unalias(array.Elem()).(*types.TypeParam)
	return !generic
}

func (c *checker) isLocalArrayIndex(addr *ssa.IndexAddr) bool {
	return arrayType(addr.X.Type()) != nil && supportedIndex(addr.Index) && c.isRecordAddress(addr.X)
}

// IsEmptySliceLiteral recognizes the zero-length backing array emitted for an
// empty slice literal or a make with zero length and capacity.
func IsEmptySliceLiteral(slice *ssa.Slice) bool {
	cell, ok := slice.X.(*ssa.Alloc)
	if !ok || Type(slice.Type()).SliceElem() == "" {
		return false
	}
	array := arrayType(cell.Type())
	return array != nil && array.Len() == 0 &&
		(slice.Low == nil || IsZero(slice.Low)) &&
		(slice.High == nil || IsZero(slice.High)) &&
		(slice.Max == nil || IsZero(slice.Max))
}

// ArrayIndexInBounds recognizes constants and dominating unsigned upper-bound guards.
func ArrayIndexInBounds(sequence, index ssa.Value, instruction ssa.Instruction) bool {
	array := arrayType(sequence.Type())
	if array == nil || array.Len() == 0 || !concreteArrayElement(array) {
		return false
	}
	if value, ok := index.(*ssa.Const); ok && value.Value != nil {
		n, exact := constant.Int64Val(value.Value)
		return exact && 0 <= n && n < array.Len()
	}
	if !Type(index.Type()).IsUnsigned() {
		return false
	}
	for block := instruction.Block().Idom(); block != nil; block = block.Idom() {
		branch, ok := block.Instrs[len(block.Instrs)-1].(*ssa.If)
		if !ok {
			continue
		}
		if block.Succs[0] == block.Succs[1] {
			continue
		}
		guard, ok := branch.Cond.(*ssa.BinOp)
		if !ok || guard.X != index {
			continue
		}
		bound, ok := guard.Y.(*ssa.Const)
		if !ok || bound.Value == nil {
			continue
		}
		n, exact := constant.Int64Val(bound.Value)
		if !exact || n != array.Len() {
			continue
		}
		safe := block.Succs[0]
		switch guard.Op {
		case token.LSS:
		case token.GEQ:
			safe = block.Succs[1]
		default:
			continue
		}
		if len(safe.Preds) == 1 && safe.Dominates(instruction.Block()) {
			return true
		}
	}
	return false
}

func arrayValueType(cell *ssa.Alloc) ir.Type {
	pointer := cell.Type().Underlying().(*types.Pointer)
	typ := Type(pointer.Elem())
	if elem, _ := typ.ArrayShape(); elem != "" {
		return typ
	}
	return ""
}

// arrayInitializer accepts only a local copy of a whole array. The copy's
// initializer dominates address formation and loads, and the cell cannot escape.
func arrayInitializer(cell *ssa.Alloc, typ ir.Type) *ssa.Store {
	var initial *ssa.Store
	for _, use := range *cell.Referrers() {
		switch use := use.(type) {
		case *ssa.Store:
			if initial != nil || use.Addr != cell || !hasType(use.Val, typ) {
				return nil
			}
			initial = use
		case *ssa.IndexAddr:
			if use.X != cell {
				return nil
			}
		default:
			if !readsCell(use, cell) {
				return nil
			}
		}
	}
	if initial == nil {
		return nil
	}
	for _, use := range *cell.Referrers() {
		if use != initial && !comesBefore(initial, use) {
			return nil
		}
	}
	return initial
}
