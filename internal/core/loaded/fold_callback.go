package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type FoldCallback struct {
	Object ObjectID
	Pos    string
}

type unwrapExpression struct {
	Program Program
	ID      ExprID
}

func unwrapParen(_ uint, state unwrapExpression) lean.FoldControl[unwrapExpression] {
	expression := state.Program.ExpressionOrMissing(state.ID)
	switch form := expression.Form.Case().(type) {
	case Parenthesized:
		next := unwrapExpression{Program: state.Program, ID: form.Inner}
		return lean.FoldControl[unwrapExpression]{State: next, Stop: false}
	case UnsupportedExpr:
		return stoppedUnwrap(state)
	case Identifier:
		return stoppedUnwrap(state)
	case UnaryExpr:
		return stoppedUnwrap(state)
	case BinaryExpr:
		return stoppedUnwrap(state)
	case SelectorExpr:
		return stoppedUnwrap(state)
	case CompositeExpr:
		return stoppedUnwrap(state)
	case KeyedExpr:
		return stoppedUnwrap(state)
	case CallExpr:
		return stoppedUnwrap(state)
	}
	return stoppedUnwrap(state)
}

func stoppedUnwrap(state unwrapExpression) lean.FoldControl[unwrapExpression] {
	return lean.FoldControl[unwrapExpression]{State: state, Stop: true}
}

func namedCallback(e Expression) ObjectID {
	switch form := e.Form.Case().(type) {
	case Identifier:
		return form.Object
	case SelectorExpr:
		if form.Selection.Kind == NoSelection {
			return form.Object
		}
		return 0
	case UnsupportedExpr:
		return 0
	case Parenthesized:
		return 0
	case UnaryExpr:
		return 0
	case BinaryExpr:
		return 0
	case CompositeExpr:
		return 0
	case KeyedExpr:
		return 0
	case CallExpr:
		return 0
	}
	return 0
}

// ResolveFoldCallback recognizes directly named, non-generic fold callbacks.
// A zero object denotes an unsupported callback.
//
//golean:export
func (p Program) ResolveFoldCallback(id ExprID) FoldCallback {
	initial := unwrapExpression{Program: p, ID: id}
	stripped := lean.FoldNUntil(p.Expressions.Size(), initial, unwrapParen)
	expr := p.ExpressionOrMissing(stripped.State.ID)
	target := namedCallback(expr)
	object := p.ObjectOrMissing(target)
	signature := p.TypeOrMissing(object.Type)
	if object.Kind != FunctionObject || object.Package == "" || object.Package == Curated || signature.Generic {
		return FoldCallback{Object: 0, Pos: expr.Pos}
	}
	return FoldCallback{Object: target, Pos: expr.Pos}
}
