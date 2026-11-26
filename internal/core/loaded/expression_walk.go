package loaded

import (
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

type ExprEffect uint8

const (
	ExprContinue ExprEffect = iota
	ExprResolveType
	ExprResolveCallee
	ExprReject
)

type exprStepKind uint8

const (
	visitExpression exprStepKind = iota + 1
	finishUnary
	beginBinaryOperands
	finishBinaryLeft
	finishBinaryRight
	beginSelectorOperand
	finishSelector
	visitConstantOperands
	finishConstant
	beginLiteralExpression
	visitLiteralField
	finishLiteralField
	resolveConversionOperand
	finishConversion
	beginCallArguments
	visitCallArgument
	finishCallArgument
)

type exprFrame struct {
	Step            exprStepKind
	ID, Left, Right ExprID
	Pos, Name       string

	Kind       uint8
	Value      CheckedExprID
	Operands   lean.Array[ExprID]
	Index      uint
	Type       TypeID
	Literal    lean.Option[exprLiteral]
	Invocation lean.Option[invocation]
}

type exprFrames struct {
	Frame exprFrame
	Rest  lean.Box[exprFrames]
}

type ExprWalk struct {
	Program Program
	Scope   BindingScope
	Value   CheckedExprID
	Nodes   lean.Array[CheckedExpr]
	Shape   CheckedType
	stack   lean.Box[exprFrames]
}

// ExprTransition reports the work a frame asks the surrounding compiler to do.
type ExprTransition struct {
	Walk       ExprWalk
	Effect     ExprEffect
	Type       TypeID
	Pos        string
	Call       CallRequest
	Diagnostic Diagnostic
}

func newExprFrame(step exprStepKind, id ExprID) exprFrame {
	return exprFrame{Step: step, ID: id, Left: 0, Right: 0, Pos: "", Name: "",
		Kind: 0, Value: 0, Operands: lean.Array[ExprID]{}, Index: 0, Type: 0, Literal: lean.None[exprLiteral](), Invocation: lean.None[invocation]()}
}

func (w ExprWalk) push(frame exprFrame) ExprWalk {
	return ExprWalk{Program: w.Program, Scope: w.Scope, Value: w.Value, Nodes: w.Nodes, Shape: w.Shape,
		stack: lean.NewBox(exprFrames{Frame: frame, Rest: w.stack})}
}

func (w ExprWalk) visit(id ExprID) ExprWalk {
	return w.push(newExprFrame(visitExpression, id))
}

// StartExpression starts lowering one expression within the current bindings.
//
//golean:export
func StartExpression(program Program, scope BindingScope, nodes lean.Array[CheckedExpr], id ExprID) ExprWalk {
	initial := ExprWalk{Program: program, Scope: scope, Value: 0, Nodes: nodes, Shape: noCheckedType(), stack: lean.Box[exprFrames]{}}
	return initial.visit(id)
}

// Pending reports whether the expression still has frames to process.
//
//golean:export
func (w ExprWalk) Pending() bool { return w.stack.IsSome() }

// WithResolvedType supplies the checked type requested by an expression.
//
//golean:export
func (w ExprWalk) WithResolvedType(shape CheckedType) ExprWalk {
	return ExprWalk{Program: w.Program, Scope: w.Scope, Value: w.Value, Nodes: w.Nodes, Shape: shape, stack: w.stack}
}

func (w ExprWalk) appendExpression(node CheckedExpr) ExprWalk {
	nodes := w.Nodes.Push(node)
	return ExprWalk{Program: w.Program, Scope: w.Scope, Value: CheckedExprID(nodes.Size()), Nodes: nodes, Shape: w.Shape, stack: w.stack}
}

func exprResult(w ExprWalk, effect ExprEffect, typ TypeID, pos string, call CallRequest, diagnostic Diagnostic) ExprTransition {
	return ExprTransition{Walk: w, Effect: effect, Type: typ, Pos: pos, Call: call, Diagnostic: diagnostic}
}

func (w ExprWalk) more() ExprTransition {
	return exprResult(w, ExprContinue, 0, "", emptyCallRequest(), validDiagnostic())
}

func (w ExprWalk) requestType(frame exprFrame, id TypeID, pos string) ExprTransition {
	return exprResult(w.push(frame), ExprResolveType, id, pos, emptyCallRequest(), validDiagnostic())
}

func (w ExprWalk) reject(issue Diagnostic) ExprTransition {
	return exprResult(w, ExprReject, 0, "", emptyCallRequest(), issue)
}

// AdvanceExpression executes one expression frame, preserving operand order.
//
//golean:export
func AdvanceExpression(w ExprWalk) ExprTransition {
	if !w.Pending() {
		return w.more()
	}
	top := w.stack.Get()
	rest := ExprWalk{Program: w.Program, Scope: w.Scope, Value: w.Value, Nodes: w.Nodes, Shape: w.Shape, stack: top.Rest}
	return rest.advance(top.Frame)
}

func (w ExprWalk) advance(frame exprFrame) ExprTransition {
	if frame.Step == visitExpression {
		return w.enter(frame.ID)
	}
	if frame.Step == finishUnary {
		return w.appendExpression(recipe(CheckedUnary, noCheckedType(), 0, "", 0, false, expressionOperands(w.Value, 0, false))).more()
	}
	if frame.Step == beginBinaryOperands {
		return w.beginBinary(frame)
	}
	if frame.Step == finishBinaryLeft {
		next := exprFrame{Step: finishBinaryRight, ID: 0, Left: 0, Right: 0,
			Pos: "", Name: frame.Name, Kind: frame.Kind, Value: w.Value, Operands: lean.Array[ExprID]{}, Index: 0, Type: 0, Literal: lean.None[exprLiteral](), Invocation: lean.None[invocation]()}
		return w.push(next).visit(frame.Right).more()
	}
	if frame.Step == finishBinaryRight {
		node := recipe(CheckedBinary, noCheckedType(), 0, frame.Name, frame.Kind, false, expressionOperands(frame.Value, w.Value, true))
		return w.appendExpression(node).more()
	}
	if frame.Step == beginSelectorOperand {
		return w.beginSelector(frame)
	}
	if frame.Step == finishSelector {
		return w.appendExpression(recipe(CheckedSelector, noCheckedType(), 0, frame.Name, frame.Kind, false, expressionOperands(w.Value, 0, false))).more()
	}
	if frame.Step == visitConstantOperands {
		return w.constantStep(frame)
	}
	if frame.Step == finishConstant {
		return w.appendExpression(recipe(CheckedConstant, w.Shape, 0, frame.Name, 0, false, lean.Array[CheckedExprID]{})).more()
	}
	if frame.Step == beginLiteralExpression {
		return w.beginLiteral(frame.ID)
	}
	if frame.Step == visitLiteralField {
		return w.visitLiteral(frame.Literal.UnwrapOr(emptyExprLiteral()))
	}
	if frame.Step == finishLiteralField {
		literal := frame.Literal.UnwrapOr(emptyExprLiteral())
		updated := exprLiteral{Type: literal.Type, Elements: literal.Elements, Fields: literal.Fields,
			Values: literal.Values.Insert(literal.Target, w.Value), Index: literal.Index + 1, Target: 0}
		return w.visitLiteral(updated)
	}
	if frame.Step == resolveConversionOperand {
		operand := w.Program.ExpressionOrMissing(frame.ID)
		return w.requestType(newExprFrame(finishConversion, frame.ID), operand.Type, operand.Pos)
	}
	if frame.Step == finishConversion {
		return w.visit(frame.ID).more()
	}
	if frame.Step == beginCallArguments {
		return w.beginInvocation(frame.Invocation.UnwrapOr(emptyInvocation()))
	}
	if frame.Step == visitCallArgument {
		return w.visitInvocationArgument(frame.Invocation.UnwrapOr(emptyInvocation()))
	}
	if frame.Step == finishCallArgument {
		return w.collectInvocationArgument(frame.Invocation.UnwrapOr(emptyInvocation()))
	}
	return w.more()
}

func (w ExprWalk) enter(id ExprID) ExprTransition {
	e := w.Program.ExpressionOrMissing(id)
	issue := e.Validate()
	if issue.Code != Valid {
		return w.reject(issue)
	}
	switch form := e.Form.Case().(type) {
	case Parenthesized:
		return w.visit(form.Inner).more()
	case Identifier:
		if e.Constant.Present {
			return w.enterConstant(e, lean.Array[ExprID]{})
		}
		binding := w.Scope.Locals.Find(form.Object)
		issue := form.ValidateBinding(binding.IsSome(), e.Pos)
		if issue.Code != Valid {
			return w.reject(issue)
		}
		return w.appendExpression(controlRecipe(CheckedLocal, binding.UnwrapOr(0), lean.Array[CheckedExprID]{}, lean.Array[CheckedMatchCase]{})).more()
	case UnaryExpr:
		if e.Constant.Present {
			return w.enterConstant(e, lean.Array[ExprID]{}.Push(form.Operand))
		}
		return w.push(newExprFrame(finishUnary, 0)).visit(form.Operand).more()
	case BinaryExpr:
		if e.Constant.Present {
			return w.enterConstant(e, lean.Array[ExprID]{}.Push(form.Left).Push(form.Right))
		}
		left := w.Program.ExpressionOrMissing(form.Left)
		frame := exprFrame{Step: beginBinaryOperands, ID: 0, Left: form.Left, Right: form.Right,
			Pos: e.Pos, Name: form.Operator, Kind: 0,
			Value: 0, Operands: lean.Array[ExprID]{}, Index: 0, Type: 0, Literal: lean.None[exprLiteral](), Invocation: lean.None[invocation]()}
		return w.requestType(frame, left.Type, left.Pos)
	case SelectorExpr:
		if e.Constant.Present {
			return w.enterConstant(e, lean.Array[ExprID]{})
		}
		base := w.Program.ExpressionOrMissing(form.Base)
		name := w.Program.ObjectOrMissing(form.Selection.Object).Name
		frame := exprFrame{Step: beginSelectorOperand, ID: form.Base, Left: 0, Right: 0,
			Pos: e.Pos, Name: name, Kind: 0, Value: 0, Operands: lean.Array[ExprID]{}, Index: 0, Type: 0, Literal: lean.None[exprLiteral](), Invocation: lean.None[invocation]()}
		return w.requestType(frame, form.Selection.Receiver, base.Pos)
	case CompositeExpr:
		if e.Constant.Present {
			return w.enterConstant(e, lean.Array[ExprID]{})
		}
		return w.requestType(newExprFrame(beginLiteralExpression, id), e.Type, e.Pos)
	case CallExpr:
		if e.Constant.Present {
			return w.enterConstant(e, form.Args)
		}
		if form.Conversion {
			return w.enterConversion(e, form)
		}
		return w.enterCall(e, form)
	case UnsupportedExpr:
		return w.enterConstant(e, lean.Array[ExprID]{})
	case KeyedExpr:
		return w.enterConstant(e, lean.Array[ExprID]{})
	}
	return w.more()
}

func (w ExprWalk) enterConstant(e Expression, operands lean.Array[ExprID]) ExprTransition {
	frame := exprFrame{Step: visitConstantOperands, ID: 0, Left: 0, Right: 0, Pos: e.Pos,
		Name: e.Constant.Value, Kind: 0, Value: 0, Operands: operands, Index: 0, Type: e.Type, Literal: lean.None[exprLiteral](), Invocation: lean.None[invocation]()}
	return w.constantStep(frame)
}

func (w ExprWalk) constantStep(frame exprFrame) ExprTransition {
	if frame.Index >= frame.Operands.Size() {
		next := exprFrame{Step: finishConstant, ID: 0, Left: 0, Right: 0, Pos: "",
			Name: frame.Name, Kind: 0, Value: 0, Operands: lean.Array[ExprID]{}, Index: 0, Type: 0, Literal: lean.None[exprLiteral](), Invocation: lean.None[invocation]()}
		return w.requestType(next, frame.Type, frame.Pos)
	}
	id := frame.Operands.Get(frame.Index).UnwrapOr(0)
	next := exprFrame{Step: visitConstantOperands, ID: 0, Left: 0, Right: 0, Pos: frame.Pos,
		Name: frame.Name, Kind: 0, Value: 0, Operands: frame.Operands, Index: frame.Index + 1, Type: frame.Type, Literal: lean.None[exprLiteral](), Invocation: lean.None[invocation]()}
	return w.push(next).visit(id).more()
}

func (w ExprWalk) beginBinary(frame exprFrame) ExprTransition {
	kind := uint8(w.Shape.Scalar)
	issue := w.Shape.ValidateBinaryOperands(frame.Name, frame.Pos)
	if issue.Code != Valid {
		return w.reject(issue)
	}
	next := exprFrame{Step: finishBinaryLeft, ID: 0, Left: 0, Right: frame.Right, Pos: "",
		Name: frame.Name, Kind: kind, Value: 0, Operands: lean.Array[ExprID]{}, Index: 0, Type: 0, Literal: lean.None[exprLiteral](), Invocation: lean.None[invocation]()}
	return w.push(next).visit(frame.Left).more()
}

func (w ExprWalk) beginSelector(frame exprFrame) ExprTransition {
	kind := selectorKind(w.Shape)
	issue := w.Shape.ValidateSelector(frame.Pos)
	if issue.Code != Valid {
		return w.reject(issue)
	}
	next := exprFrame{Step: finishSelector, ID: 0, Left: 0, Right: 0, Pos: "",
		Name: frame.Name, Kind: kind, Value: 0, Operands: lean.Array[ExprID]{}, Index: 0, Type: 0, Literal: lean.None[exprLiteral](), Invocation: lean.None[invocation]()}
	return w.push(next).visit(frame.ID).more()
}

func selectorKind(shape CheckedType) uint8 {
	if shape.Kind == CuratedShape && shape.Curated == CuratedFoldControl {
		return 1
	}
	return 0
}

func (w ExprWalk) enterConversion(e Expression, call CallExpr) ExprTransition {
	issue := w.Program.CheckConversion(e, call)
	if issue.Code != Valid {
		return w.reject(issue)
	}
	id := call.Args.Get(0).UnwrapOr(0)
	return w.requestType(newExprFrame(resolveConversionOperand, id), e.Type, e.Pos)
}
