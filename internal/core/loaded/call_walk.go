package loaded

import (
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

type CallRequest struct {
	Target ObjectID
	Pos    string
	Fold   FoldFlavor
	Values lean.Array[CheckedExprID]
}

func emptyCallRequest() CallRequest {
	return CallRequest{Target: 0, Pos: "", Fold: 0, Values: lean.Array[CheckedExprID]{}}
}

type invocationKind uint8

const (
	invokeFunction invocationKind = iota + 1
	invokeConstructor
	invokePrimitive
	invokeFold
)

type invocation struct {
	Kind         invocationKind
	Target       ObjectID
	Name, Pos    string
	Receiver     ExprID
	Args         lean.Array[ExprID]
	Index, Count uint
	Type         CheckedType
	Values       lean.Array[CheckedExprID]
	Primitive    PrimitiveOp
	Fold         FoldFlavor
}

func emptyInvocation() invocation {
	return invocation{Kind: 0, Target: 0, Name: "", Pos: "", Receiver: 0, Args: lean.Array[ExprID]{},
		Index: 0, Count: 0, Type: noCheckedType(), Values: lean.Array[CheckedExprID]{}, Primitive: 0, Fold: 0}
}

func callFrame(step exprStepKind, call invocation) exprFrame {
	return exprFrame{Step: step, ID: 0, Left: 0, Right: 0, Pos: "", Name: "", Kind: 0,
		Value: 0, Operands: lean.Array[ExprID]{}, Index: 0, Type: 0,
		Literal: lean.None[exprLiteral](), Invocation: lean.Some(call)}
}

func (w ExprWalk) enterCall(e Expression, form CallExpr) ExprTransition {
	object := w.Program.ObjectOrMissing(form.Object)
	issue := form.ValidateTarget(object, e.Pos)
	if issue.Code != Valid {
		return w.reject(issue)
	}
	if object.Constructor.IsSome() {
		found := object.Constructor.UnwrapOr(EnumConstructor{Owner: 0, Variant: ""})
		owner := w.Program.ObjectOrMissing(found.Owner)
		call := invocation{Kind: invokeConstructor, Target: found.Owner, Name: found.Variant, Pos: e.Pos,
			Receiver: 0, Args: form.Args, Index: 0, Count: 1, Type: noCheckedType(), Values: lean.Array[CheckedExprID]{}, Primitive: 0, Fold: 0}
		return w.requestType(callFrame(beginCallArguments, call), owner.Type, e.Pos)
	}
	if object.Package == Curated {
		return w.enterCuratedCall(e, form, object.Name)
	}
	receiver := form.ValidateReceiver(w.Program.TypeOrMissing(object.Type), e.Pos)
	if receiver.Code != Valid {
		return w.reject(receiver)
	}
	call := invocation{Kind: invokeFunction, Target: form.Object, Name: object.Name, Pos: e.Pos,
		Receiver: form.Receiver, Args: form.Args, Index: 0, Count: invocationCount(form), Type: noCheckedType(),
		Values: lean.Array[CheckedExprID]{}, Primitive: 0, Fold: 0}
	return w.visitInvocationArgument(call)
}

func invocationCount(form CallExpr) uint {
	if form.Receiver != 0 {
		return form.Args.Size() + 1
	}
	return form.Args.Size()
}

func (w ExprWalk) enterCuratedCall(e Expression, form CallExpr, name string) ExprTransition {
	if form.Selection.Kind == NoSelection {
		fold := foldKind(name)
		if fold != 0 {
			return w.enterFold(e, form, fold)
		}
		op := CuratedConstructor(name)
		if op == 0 {
			return w.rejectPrimitive(e.Pos, name)
		}
		call := primitiveInvocation(e, form, name, op)
		return w.requestType(callFrame(beginCallArguments, call), e.Type, e.Pos)
	}
	if form.Receiver != 0 && form.Selection.Direct {
		base := w.Program.ExpressionOrMissing(form.Receiver)
		named := w.Program.Unalias(form.Selection.Receiver)
		receiver := w.Program.ObjectOrMissing(named.Object)
		op := CuratedMethod(receiver.Name, name)
		call := primitiveInvocation(e, form, name, op)
		return w.requestType(callFrame(beginCallArguments, call), form.Selection.Receiver, base.Pos)
	}
	return w.rejectPrimitive(e.Pos, name)
}

func primitiveInvocation(e Expression, form CallExpr, name string, op PrimitiveOp) invocation {
	return invocation{Kind: invokePrimitive, Target: form.Object, Name: name, Pos: e.Pos, Receiver: form.Receiver,
		Args: form.Args, Index: 0, Count: invocationCount(form), Type: noCheckedType(), Values: lean.Array[CheckedExprID]{}, Primitive: op, Fold: 0}
}

func (w ExprWalk) rejectPrimitive(pos string, name string) ExprTransition {
	return w.reject(Diagnostic{Code: UnsupportedCuratedOperation, Pos: pos, Detail: name})
}

func foldKind(name string) FoldFlavor {
	if name == "FoldN" {
		return CheckedFoldN
	}
	if name == "FoldNUntil" {
		return CheckedFoldNUntil
	}
	if name == "FoldList" {
		return CheckedFoldList
	}
	if name == "FoldListUntil" {
		return CheckedFoldListUntil
	}
	return 0
}

func (w ExprWalk) enterFold(e Expression, form CallExpr, kind FoldFlavor) ExprTransition {
	step := w.Program.ResolveFoldCallback(form.Args.Get(2).UnwrapOr(0))
	if step.Object == 0 {
		return w.reject(Diagnostic{Code: InvalidFoldCallback, Pos: step.Pos, Detail: ""})
	}
	call := invocation{Kind: invokeFold, Target: step.Object, Name: "", Pos: step.Pos, Receiver: 0,
		Args: form.Args, Index: 0, Count: 2, Type: noCheckedType(), Values: lean.Array[CheckedExprID]{}, Primitive: 0, Fold: kind}
	return w.requestType(callFrame(beginCallArguments, call), e.Type, e.Pos)
}

func (w ExprWalk) beginInvocation(call invocation) ExprTransition {
	if call.Kind == invokePrimitive && call.Primitive == 0 {
		return w.rejectPrimitive(call.Pos, call.Name)
	}
	ready := invocation{Kind: call.Kind, Target: call.Target, Name: call.Name, Pos: call.Pos, Receiver: call.Receiver,
		Args: call.Args, Index: call.Index, Count: call.Count, Type: w.Shape, Values: call.Values, Primitive: call.Primitive, Fold: call.Fold}
	return w.visitInvocationArgument(ready)
}

func invocationArgument(call invocation) ExprID {
	if call.Receiver == 0 {
		return call.Args.Get(call.Index).UnwrapOr(0)
	}
	if call.Index == 0 {
		return call.Receiver
	}
	return call.Args.Get(call.Index - 1).UnwrapOr(0)
}

func (w ExprWalk) visitInvocationArgument(call invocation) ExprTransition {
	if call.Index >= call.Count {
		return w.finishInvocation(call)
	}
	return w.push(callFrame(finishCallArgument, call)).visit(invocationArgument(call)).more()
}

func (w ExprWalk) collectInvocationArgument(call invocation) ExprTransition {
	next := invocation{Kind: call.Kind, Target: call.Target, Name: call.Name, Pos: call.Pos, Receiver: call.Receiver,
		Args: call.Args, Index: call.Index + 1, Count: call.Count, Type: call.Type,
		Values: call.Values.Push(w.Value), Primitive: call.Primitive, Fold: call.Fold}
	return w.push(callFrame(visitCallArgument, next)).more()
}

func (w ExprWalk) finishInvocation(call invocation) ExprTransition {
	if call.Kind == invokeConstructor {
		return w.appendExpression(recipe(CheckedConstructor, call.Type, call.Target, call.Name, 0, false, call.Values)).more()
	}
	if call.Kind == invokePrimitive {
		return w.appendExpression(recipe(CheckedPrimitive, call.Type, 0, "", uint8(call.Primitive), false, call.Values)).more()
	}
	request := CallRequest{Target: call.Target, Pos: call.Pos, Fold: call.Fold, Values: call.Values}
	return exprResult(w, ExprResolveCallee, 0, call.Pos, request, validDiagnostic())
}

// WithResolvedCall records a call whose dependency has passed checking.
//
//golean:export
func (w ExprWalk) WithResolvedCall(request CallRequest, abstract bool) ExprWalk {
	return w.appendExpression(recipe(CheckedCall, noCheckedType(), request.Target, "", uint8(request.Fold), abstract, request.Values))
}
