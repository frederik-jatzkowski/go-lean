package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type CheckedExprID uint
type CheckedExprKind uint8

const (
	CheckedConstant CheckedExprKind = iota + 1
	CheckedLocal
	CheckedUnary
	CheckedBinary
	CheckedSelector
	CheckedComposite
	CheckedEmpty
	CheckedZero
	CheckedConstructor
	CheckedPrimitive
	CheckedCall
	CheckedIf
	CheckedLet
	CheckedJoin
	CheckedJump
	CheckedMatch
)

type FoldFlavor uint8

const (
	CheckedFoldN FoldFlavor = 1 << iota
	CheckedFoldNUntil
	CheckedFoldList
	CheckedFoldListUntil
)

// CheckedExpr records the operation and operand identities established by
// checking. Operands are one-based indices into the expression's checked nodes.
type CheckedExpr struct {
	Kind      CheckedExprKind
	Type      CheckedType
	Object    ObjectID
	Name      string
	Operation uint8
	Abstract  bool
	Arguments lean.Array[CheckedExprID]
	Binding   int
	Cases     lean.Array[CheckedMatchCase]
}

func recipe(kind CheckedExprKind, t CheckedType, object ObjectID, name string, operation uint8, abstract bool, arguments lean.Array[CheckedExprID]) CheckedExpr {
	return CheckedExpr{Kind: kind, Type: t, Object: object, Name: name, Operation: operation, Abstract: abstract, Arguments: arguments, Binding: 0, Cases: lean.Array[CheckedMatchCase]{}}
}

func expressionOperands(first CheckedExprID, second CheckedExprID, two bool) lean.Array[CheckedExprID] {
	firstOnly := lean.Array[CheckedExprID]{}.Push(first)
	if two {
		return firstOnly.Push(second)
	}
	return firstOnly
}

type CheckedMatchCase struct {
	Variant string
	Binding int
	Value   CheckedExprID
}

type CheckedLetBinding struct {
	Binding int
	Value   CheckedExprID
}

func controlRecipe(kind CheckedExprKind, binding int, args lean.Array[CheckedExprID], cases lean.Array[CheckedMatchCase]) CheckedExpr {
	return CheckedExpr{Kind: kind, Type: noCheckedType(), Object: 0, Name: "", Operation: 0, Abstract: false,
		Arguments: args, Binding: binding, Cases: cases}
}
