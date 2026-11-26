package loaded

import (
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

type exprLiteral struct {
	Type          CheckedType
	Elements      lean.Array[ExprID]
	Fields        lean.Array[ObjectID]
	Values        lean.OrderedMap[uint, CheckedExprID]
	Index, Target uint
}

func emptyExprLiteral() exprLiteral {
	return exprLiteral{Type: noCheckedType(), Elements: lean.Array[ExprID]{}, Fields: lean.Array[ObjectID]{},
		Values: lean.OrderedMap[uint, CheckedExprID]{}, Index: 0, Target: 0}
}

func (w ExprWalk) beginLiteral(id ExprID) ExprTransition {
	e := w.Program.ExpressionOrMissing(id)
	switch form := e.Form.Case().(type) {
	case CompositeExpr:
		return w.prepareLiteral(e, form)
	case UnsupportedExpr:
		return w.more()
	case Parenthesized:
		return w.more()
	case Identifier:
		return w.more()
	case UnaryExpr:
		return w.more()
	case BinaryExpr:
		return w.more()
	case SelectorExpr:
		return w.more()
	case KeyedExpr:
		return w.more()
	case CallExpr:
		return w.more()
	}
	return w.more()
}

func (w ExprWalk) prepareLiteral(e Expression, literal CompositeExpr) ExprTransition {
	checked := w.Program.CheckComposite(e.Type, w.Shape, e.Pos, literal.Elements.Size())
	if checked.Diagnostic.Code != Valid {
		return w.reject(checked.Diagnostic)
	}
	if checked.Kind == CompositeEnumZero {
		return w.appendExpression(recipe(CheckedZero, w.Shape, 0, "", 0, false, lean.Array[CheckedExprID]{})).more()
	}
	if checked.Kind == CompositeEmpty {
		return w.appendExpression(recipe(CheckedEmpty, w.Shape, 0, "", 0, false, lean.Array[CheckedExprID]{})).more()
	}
	initial := exprLiteral{Type: w.Shape, Elements: literal.Elements, Fields: checked.Fields,
		Values: lean.OrderedMap[uint, CheckedExprID]{}, Index: 0, Target: 0}
	return w.push(literalFrame(visitLiteralField, initial)).more()
}

func literalFrame(step exprStepKind, literal exprLiteral) exprFrame {
	return exprFrame{Step: step, ID: 0, Left: 0, Right: 0, Pos: "", Name: "", Kind: 0,
		Value: 0, Operands: lean.Array[ExprID]{}, Index: 0, Type: 0, Literal: lean.Some(literal), Invocation: lean.None[invocation]()}
}

func (w ExprWalk) visitLiteral(literal exprLiteral) ExprTransition {
	if literal.Index >= literal.Elements.Size() {
		return w.appendExpression(finishLiteral(literal)).more()
	}
	id := literal.Elements.Get(literal.Index).UnwrapOr(0)
	item := w.Program.CheckKeyedElement(id, literal.Fields)
	if item.Diagnostic.Code != Valid {
		return w.reject(item.Diagnostic)
	}
	if !item.Found {
		next := exprLiteral{Type: literal.Type, Elements: literal.Elements, Fields: literal.Fields, Values: literal.Values,
			Index: literal.Index + 1, Target: 0}
		return w.push(literalFrame(visitLiteralField, next)).more()
	}
	pending := exprLiteral{Type: literal.Type, Elements: literal.Elements, Fields: literal.Fields, Values: literal.Values,
		Index: literal.Index, Target: item.Index}
	return w.push(literalFrame(finishLiteralField, pending)).visit(item.Value).more()
}

type fieldValues struct {
	Values   lean.OrderedMap[uint, CheckedExprID]
	Sequence lean.Array[CheckedExprID]
}

func appendFieldValue(index uint, state fieldValues) fieldValues {
	value := state.Values.Find(index).UnwrapOr(0)
	return fieldValues{Values: state.Values, Sequence: state.Sequence.Push(value)}
}

func finishLiteral(literal exprLiteral) CheckedExpr {
	initial := fieldValues{Values: literal.Values, Sequence: lean.Array[CheckedExprID]{}}
	fields := lean.FoldN(literal.Fields.Size(), initial, appendFieldValue)
	return recipe(CheckedComposite, literal.Type, literal.Type.Object, "", 0, false, fields.Sequence)
}
