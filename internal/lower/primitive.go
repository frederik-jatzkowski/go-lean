package lower

import (
	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

func (f *function) primitive(op loaded.PrimitiveOp, t ir.Type, args []ir.Expr) ir.Expr {
	var fallback ir.Expr
	if op == loaded.OpBoxRead {
		fallback = f.zero(t.Case().(ir.BoxType).Element)
	}
	return ir.PrimitiveFromOperation(op, t, lean.ArrayFromSlice(args), fallback)
}
