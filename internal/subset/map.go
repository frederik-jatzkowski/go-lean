package subset

import (
	"go/ast"
	"go/token"
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

// freshMapResult checks that every return yields the same allocation and that
// only local reads and writes can observe it before return.
func freshMapResult(fn *ssa.Function, index int) *ssa.MakeMap {
	var fresh *ssa.MakeMap
	for _, block := range fn.Blocks {
		ret, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Return)
		if !ok {
			continue
		}
		allocation, ok := ret.Results[index].(*ssa.MakeMap)
		if !ok || fresh != nil && fresh != allocation {
			return nil
		}
		fresh = allocation
	}
	if fresh == nil || fresh.Reserve != nil && !supportedIndex(fresh.Reserve) {
		return nil
	}
	literalKeys := mapLiteralUpdates(fn, fresh.Pos())
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
			if literalKeys[use.Pos()] {
				if _, ok := use.Key.(*ssa.Const); !ok {
					return nil
				}
			}
		case *ssa.Return:
			for position, value := range use.Results {
				if value == fresh && position != index {
					return nil
				}
			}
		default:
			return nil
		}
	}
	return fresh
}

// Go leaves assignment order within a map literal unspecified. For literals
// with multiple entries, require constant keys, which Go checks for duplicates.
func mapLiteralUpdates(fn *ssa.Function, pos token.Pos) map[token.Pos]bool {
	if fn.Syntax() == nil || !pos.IsValid() {
		return nil
	}
	var updates map[token.Pos]bool
	ast.Inspect(fn.Syntax(), func(node ast.Node) bool {
		literal, ok := node.(*ast.CompositeLit)
		if !ok || literal.Lbrace != pos || len(literal.Elts) < 2 {
			return true
		}
		updates = make(map[token.Pos]bool, len(literal.Elts))
		for _, element := range literal.Elts {
			if pair, ok := element.(*ast.KeyValueExpr); ok {
				updates[pair.Colon] = true
			}
		}
		return false
	})
	return updates
}
