package lower

import (
	"go/ast"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
)

var folds = map[string]ir.FoldKind{
	"FoldN": ir.FoldN, "FoldNUntil": ir.FoldNUntil,
	"FoldList": ir.FoldList, "FoldListUntil": ir.FoldListUntil,
}

func (f *function) fold(e *ast.CallExpr, kind ir.FoldKind) (ir.Expr, error) {
	p := f.source.Package
	step := ast.Unparen(e.Args[2])
	var fn *types.Func
	switch target := step.(type) {
	case *ast.Ident:
		fn, _ = p.TypesInfo.Uses[target].(*types.Func)
	case *ast.SelectorExpr:
		if p.TypesInfo.Selections[target] == nil {
			fn, _ = p.TypesInfo.Uses[target.Sel].(*types.Func)
		}
	}
	if fn == nil || fn.Pkg() == nil || fn.Pkg().Path() == load.Curated ||
		fn.Type().(*types.Signature).TypeParams().Len() != 0 {
		return ir.Expr{}, load.Error(p, step.Pos(), "fold step must be a directly named, non-generic function")
	}
	if _, err := f.goType(p, e.Pos(), p.TypesInfo.TypeOf(e)); err != nil {
		return ir.Expr{}, err
	}
	args, err := f.arguments(e.Args[:2])
	if err != nil {
		return ir.Expr{}, err
	}
	abstract, err := f.callTarget(fn, step.Pos())
	if err != nil {
		return ir.Expr{}, err
	}
	f.output(p.PkgPath).Folds |= kind
	target := ir.NewFoldStepDirectStep(ir.DirectStep{Target: symbol(fn)})
	if abstract {
		target = ir.NewFoldStepAbstractStep(ir.AbstractStep{Target: symbol(fn)})
	}
	var fold ir.Fold
	switch kind {
	case ir.FoldN:
		fold = ir.NewFoldCountFold(ir.CountFold{Count: args[0], Initial: args[1], Step: target})
	case ir.FoldNUntil:
		fold = ir.NewFoldCountUntilFold(ir.CountUntilFold{Count: args[0], Initial: args[1], Step: target})
	case ir.FoldList:
		fold = ir.NewFoldListFold(ir.ListFold{Items: args[0], Initial: args[1], Step: target})
	case ir.FoldListUntil:
		fold = ir.NewFoldListUntilFold(ir.ListUntilFold{Items: args[0], Initial: args[1], Step: target})
	default:
		panic("unknown fold kind")
	}
	return ir.NewExprFoldExpr(ir.FoldExpr{Fold: fold}), nil
}
