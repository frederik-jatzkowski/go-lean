package lower

import (
	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
)

var folds = map[string]ir.FoldKind{
	"FoldN": ir.FoldN, "FoldNUntil": ir.FoldNUntil,
	"FoldList": ir.FoldList, "FoldListUntil": ir.FoldListUntil,
}

func (f *function) fold(e loaded.Expression, call loaded.CallExpr, kind ir.FoldKind) (ir.Expr, error) {
	p := f.pkg
	step := f.inputExpr(at(call.Args, uint(2)))
	for inner, ok := step.Form.Case().(loaded.Parenthesized); ok; inner, ok = step.Form.Case().(loaded.Parenthesized) {
		step = f.inputExpr(inner.Inner)
	}
	var fn loaded.ObjectID
	switch form := step.Form.Case().(type) {
	case loaded.Identifier:
		fn = form.Object
	case loaded.SelectorExpr:
		if form.Selection.Kind == loaded.NoSelection {
			fn = form.Object
		}
	}

	obj := f.object(fn)
	if obj.Kind != loaded.FunctionObject || obj.Package == "" || obj.Package == loaded.Curated || f.inputType(obj.Type).Generic {
		return ir.Expr{}, diagnostic(step.Pos, "fold step must be a directly named, non-generic function")
	}
	if _, err := f.goType(p, e.Pos, e.Type); err != nil {
		return ir.Expr{}, err
	}
	args, err := f.arguments([]loaded.ExprID{at(call.Args, uint(0)), at(call.Args, uint(1))})
	if err != nil {
		return ir.Expr{}, err
	}
	abstract, err := f.callTarget(fn, step.Pos)
	if err != nil {
		return ir.Expr{}, err
	}
	f.output(p.Path).Folds |= kind
	return ir.FoldFromOperation(kind, args[0], args[1], f.symbol(fn), abstract), nil
}
