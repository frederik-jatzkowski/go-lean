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
	if (key.IsInteger() || key == ir.Bytes) && value.IsInteger() {
		return ir.MapType(key, value)
	}
	return ""
}

func supportedMapLookup(lookup *ssa.Lookup) bool {
	key, _ := Type(lookup.X.Type()).MapShape()
	return key != "" && supportedValue(lookup.X) && hasType(lookup.Index, key)
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
