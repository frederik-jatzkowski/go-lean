package subset

import (
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

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
