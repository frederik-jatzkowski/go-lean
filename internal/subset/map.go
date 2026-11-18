package subset

import (
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

func mapType(m *types.Map) ir.Type {
	key, value := Type(m.Key()), Type(m.Elem())
	if key.IsInteger() && value.IsInteger() {
		return ir.MapType(key, value)
	}
	return ""
}

func supportedMapLookup(lookup *ssa.Lookup) bool {
	key, _ := Type(lookup.X.Type()).MapShape()
	return key != "" && supportedValue(lookup.X) && hasType(lookup.Index, key)
}

// freshMapResult checks that the returned allocation is used only for local
// reads and writes before return. A single block gives the updates one order.
func freshMapResult(fn *ssa.Function) *ssa.MakeMap {
	if len(fn.Blocks) != 1 {
		return nil
	}
	block := fn.Blocks[0]
	ret, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Return)
	if !ok {
		return nil
	}
	fresh, ok := ret.Results[0].(*ssa.MakeMap)
	if !ok || fresh.Block() != block || fresh.Reserve != nil {
		return nil
	}
	for _, use := range *fresh.Referrers() {
		switch use := use.(type) {
		case *ssa.Lookup:
			if use.X != fresh {
				return nil
			}
		case *ssa.MapUpdate:
			if use.Map != fresh {
				return nil
			}
		case *ssa.Return:
			if use != ret {
				return nil
			}
		default:
			return nil
		}
	}
	return fresh
}
