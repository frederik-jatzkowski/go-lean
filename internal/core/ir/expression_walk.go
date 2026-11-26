package ir

import (
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

func binaryOperator(operator string) BinaryOp {
	if operator == "+" {
		return Add
	}
	if operator == "-" {
		return Sub
	}
	if operator == "==" {
		return Eq
	}
	if operator == "!=" {
		return Ne
	}
	if operator == "<" {
		return Lt
	}
	if operator == "<=" {
		return Le
	}
	if operator == ">" {
		return Gt
	}
	if operator == ">=" {
		return Ge
	}
	if operator == "&&" {
		return And
	}
	if operator == "||" {
		return Or
	}
	return 0
}

func selectorValue(kind Kind, field string, value Expr) Expr {
	if kind == FoldControl {
		if field == "Stop" {
			return NewExprFoldStopRead(FoldStopRead{Control: value})
		}
		return NewExprFoldStateRead(FoldStateRead{Control: value})
	}
	return NewExprFieldRead(FieldRead{Record: value, Name: field})
}

type checkedArgs struct {
	IDs    lean.Array[loaded.CheckedExprID]
	Nodes  lean.Array[Expr]
	Values lean.Array[Expr]
}

func checkedOperand(nodes lean.Array[Expr], id loaded.CheckedExprID) Expr {
	if id == 0 {
		return Expr{}
	}
	return nodes.Get(uint(id) - 1).UnwrapOr(Expr{})
}

func takeCheckedOperand(index uint, state checkedArgs) checkedArgs {
	value := checkedOperand(state.Nodes, state.IDs.Get(index).UnwrapOr(0))
	return checkedArgs{IDs: state.IDs, Nodes: state.Nodes, Values: state.Values.Push(value)}
}

func expressionSequence(values lean.Array[Expr]) ExprSeq {
	initial := zeroSequence{Values: values, Result: ExprSeq{First: lean.Box[ExprSeqItem]{}}}
	return lean.FoldN(values.Size(), initial, prependZeroValue).Result
}

// ExpressionFromChecked constructs a node from checked facts and its already
// lowered operands. The surrounding compiler supplies symbols and zero values.
//
//golean:export
func ExpressionFromChecked(node loaded.CheckedExpr, nodes lean.Array[Expr], t Type, symbol Symbol, zero Expr) Expr {
	initial := checkedArgs{IDs: node.Arguments, Nodes: nodes, Values: lean.Array[Expr]{}}
	args := lean.FoldN(node.Arguments.Size(), initial, takeCheckedOperand).Values
	first := args.Get(0).UnwrapOr(Expr{})
	second := args.Get(1).UnwrapOr(Expr{})
	if node.Kind == loaded.CheckedConstant {
		return NewExprConstant(Constant{Type: t, Value: node.Name})
	}
	if node.Kind == loaded.CheckedLocal {
		return NewExprLocal(Local{ID: node.Binding})
	}
	if node.Kind == loaded.CheckedUnary {
		return NewExprUnary(Unary{Op: Not, Value: first})
	}
	if node.Kind == loaded.CheckedBinary {
		kind := ScalarFromLoaded(loaded.ScalarKind(node.Operation)).Kind()
		return NewExprBinary(Binary{Op: binaryOperator(node.Name), Kind: kind, Left: first, Right: second})
	}
	if node.Kind == loaded.CheckedSelector {
		if node.Operation == 1 {
			return selectorValue(FoldControl, node.Name, first)
		}
		return selectorValue(Record, node.Name, first)
	}
	if node.Kind == loaded.CheckedComposite {
		if node.Type.Curated == loaded.CuratedFoldControl {
			return NewExprFoldControlLiteral(FoldControlLiteral{State: first, Stop: second})
		}
		return NewExprStructLiteral(StructLiteral{Type: symbol, Fields: expressionSequence(args)})
	}
	if node.Kind == loaded.CheckedEmpty {
		return NewEmptyValueExpr(t)
	}
	if node.Kind == loaded.CheckedZero {
		return zero
	}
	if node.Kind == loaded.CheckedConstructor {
		return NewExprConstructor(Constructor{Enum: symbol, Variant: node.Name, Value: first})
	}
	if node.Kind == loaded.CheckedPrimitive {
		return PrimitiveFromOperation(loaded.PrimitiveOp(node.Operation), t, args, zero)
	}
	if node.Kind == loaded.CheckedCall {
		if node.Operation != 0 {
			return FoldFromOperation(FoldKind(node.Operation), first, second, symbol, node.Abstract)
		}
		if node.Abstract {
			return NewExprAbstractCall(AbstractCall{Target: symbol, Args: expressionSequence(args)})
		}
		return NewExprCall(Call{Target: symbol, Args: expressionSequence(args)})
	}
	if node.Kind == loaded.CheckedIf {
		return NewExprIf(If{Cond: first, Then: second, Else: args.Get(2).UnwrapOr(Expr{})})
	}
	if node.Kind == loaded.CheckedLet {
		return NewExprLet(Let{ID: node.Binding, Value: first, Body: second})
	}
	if node.Kind == loaded.CheckedJoin {
		return NewExprJoin(Join{ID: node.Binding, Next: first, Body: second})
	}
	if node.Kind == loaded.CheckedJump {
		return NewExprJump(Jump{ID: node.Binding})
	}
	if node.Kind == loaded.CheckedMatch {
		initial := checkedMatchBuild{Cases: node.Cases, Nodes: nodes, Result: MatchSeq{First: lean.Box[MatchSeqItem]{}}}
		sequence := lean.FoldN(node.Cases.Size(), initial, prependCheckedCase).Result
		return NewExprMatch(Match{Value: first, Cases: sequence})
	}
	return Expr{}
}

type checkedMatchBuild struct {
	Cases  lean.Array[loaded.CheckedMatchCase]
	Nodes  lean.Array[Expr]
	Result MatchSeq
}

func prependCheckedCase(index uint, state checkedMatchBuild) checkedMatchBuild {
	item := state.Cases.Get(state.Cases.Size() - 1 - index).UnwrapOr(loaded.CheckedMatchCase{Variant: "", Binding: -1, Value: 0})
	arm := MatchCase{Variant: item.Variant, Binding: item.Binding, Body: checkedOperand(state.Nodes, item.Value)}
	result := MatchSeq{First: lean.NewBox(MatchSeqItem{Value: arm, Rest: state.Result})}
	return checkedMatchBuild{Cases: state.Cases, Nodes: state.Nodes, Result: result}
}
