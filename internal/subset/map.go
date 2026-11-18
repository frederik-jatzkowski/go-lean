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
