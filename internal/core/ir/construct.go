package ir

import (
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

func primitiveExpr(value Primitive) Expr {
	return NewExprPrimitiveExpr(PrimitiveExpr{Primitive: value})
}

//golean:export
func NewEmptyValueExpr(t Type) Expr {
	return primitiveExpr(NewPrimitiveEmptyValue(EmptyValue{Type: t}))
}

// PrimitiveFromOperation constructs a primitive expression from its resolved
// operation, type, arguments, and Box.Get zero fallback.
//
//golean:export
func PrimitiveFromOperation(op loaded.PrimitiveOp, t Type, args lean.Array[Expr], fallback Expr) Expr {
	first := args.Get(0).UnwrapOr(Expr{})
	second := args.Get(1).UnwrapOr(Expr{})
	third := args.Get(2).UnwrapOr(Expr{})
	if op == loaded.OpMakeSome {
		return primitiveExpr(NewPrimitiveMakeSome(MakeSome{Value: first}))
	}
	if op == loaded.OpMakeNone {
		return primitiveExpr(NewPrimitiveMakeNone(MakeNone{Type: t}))
	}
	if op == loaded.OpListNil {
		return primitiveExpr(NewPrimitiveListNil(ListNil{Type: t}))
	}
	if op == loaded.OpListCons {
		return primitiveExpr(NewPrimitiveListCons(ListCons{Head: first, Tail: second}))
	}
	if op == loaded.OpListIsEmpty {
		return primitiveExpr(NewPrimitiveListIsEmpty(ListIsEmpty{Items: first}))
	}
	if op == loaded.OpOptionIsSome {
		return primitiveExpr(NewPrimitiveOptionIsSome(OptionIsSome{Option: first}))
	}
	if op == loaded.OpOptionUnwrapOr {
		return primitiveExpr(NewPrimitiveOptionUnwrapOr(OptionUnwrapOr{Option: first, Fallback: second}))
	}
	if op == loaded.OpBoxRead {
		return primitiveExpr(NewPrimitiveBoxRead(BoxRead{Box: first, Fallback: fallback}))
	}
	if op == loaded.OpArrayPush {
		return primitiveExpr(NewPrimitiveArrayPush(ArrayPush{Array: first, Value: second}))
	}
	if op == loaded.OpByteArrayPush {
		return primitiveExpr(NewPrimitiveByteArrayPush(ByteArrayPush{Bytes: first, Value: second}))
	}
	if op == loaded.OpArrayPop {
		return primitiveExpr(NewPrimitiveArrayPop(ArrayPop{Array: first}))
	}
	if op == loaded.OpArrayGet {
		return primitiveExpr(NewPrimitiveArrayGet(ArrayGet{Array: first, Index: second}))
	}
	if op == loaded.OpByteArrayGet {
		return primitiveExpr(NewPrimitiveByteArrayGet(ByteArrayGet{Bytes: first, Index: second}))
	}
	if op == loaded.OpBitVecGet {
		return primitiveExpr(NewPrimitiveBitVecGet(BitVecGet{Bits: first, Index: second}))
	}
	if op == loaded.OpArraySet {
		return primitiveExpr(NewPrimitiveArraySet(ArraySet{Array: first, Index: second, Value: third}))
	}
	if op == loaded.OpByteArraySet {
		return primitiveExpr(NewPrimitiveByteArraySet(ByteArraySet{Bytes: first, Index: second, Value: third}))
	}
	if op == loaded.OpBitVecSet {
		return primitiveExpr(NewPrimitiveBitVecSet(BitVecSet{Type: t, Bits: first, Index: second, Value: third}))
	}
	if op == loaded.OpCollectionSize {
		return primitiveExpr(NewPrimitiveCollectionSize(CollectionSize{Collection: first}))
	}
	if op == loaded.OpByteArrayExtract {
		return primitiveExpr(NewPrimitiveByteArrayExtract(ByteArrayExtract{Bytes: first, Start: second, End: third}))
	}
	if op == loaded.OpMapFind {
		return primitiveExpr(NewPrimitiveMapFind(MapFind{Map: first, Key: second}))
	}
	if op == loaded.OpMapContains {
		return primitiveExpr(NewPrimitiveMapContains(MapContains{Map: first, Key: second}))
	}
	if op == loaded.OpMapInsert {
		return primitiveExpr(NewPrimitiveMapInsert(MapInsert{Map: first, Key: second, Value: third}))
	}
	if op == loaded.OpMapErase {
		return primitiveExpr(NewPrimitiveMapErase(MapErase{Map: first, Key: second}))
	}
	if op == loaded.OpSetContains {
		return primitiveExpr(NewPrimitiveSetContains(SetContains{Set: first, Key: second}))
	}
	if op == loaded.OpSetInsert {
		return primitiveExpr(NewPrimitiveSetInsert(SetInsert{Set: first, Key: second}))
	}
	if op == loaded.OpSetErase {
		return primitiveExpr(NewPrimitiveSetErase(SetErase{Set: first, Key: second}))
	}
	if op == loaded.OpMakeBitVec {
		return primitiveExpr(NewPrimitiveMakeBitVec(MakeBitVec{Width: first, Value: second}))
	}
	if op == loaded.OpBitVecWidth {
		return primitiveExpr(NewPrimitiveBitVecWidth(BitVecWidth{Bits: first}))
	}
	if op == loaded.OpBitVecToUint64 {
		return primitiveExpr(NewPrimitiveBitVecToUint64(BitVecToUint64{Bits: first}))
	}
	return Expr{}
}

// ScalarFromLoaded constructs the IR type for a supported Go scalar.
//
//golean:export
func ScalarFromLoaded(s loaded.ScalarKind) Type {
	if s == loaded.ScalarBool {
		return NewTypeScalarType(ScalarType{Scalar: Bool})
	}
	if s == loaded.ScalarString {
		return NewTypeScalarType(ScalarType{Scalar: String})
	}
	if s == loaded.ScalarInt8 {
		return NewTypeScalarType(ScalarType{Scalar: Int8})
	}
	if s == loaded.ScalarInt16 {
		return NewTypeScalarType(ScalarType{Scalar: Int16})
	}
	if s == loaded.ScalarInt32 {
		return NewTypeScalarType(ScalarType{Scalar: Int32})
	}
	if s == loaded.ScalarInt64 {
		return NewTypeScalarType(ScalarType{Scalar: Int64})
	}
	if s == loaded.ScalarUInt8 {
		return NewTypeScalarType(ScalarType{Scalar: UInt8})
	}
	if s == loaded.ScalarUInt16 {
		return NewTypeScalarType(ScalarType{Scalar: UInt16})
	}
	if s == loaded.ScalarUInt32 {
		return NewTypeScalarType(ScalarType{Scalar: UInt32})
	}
	if s == loaded.ScalarUInt64 {
		return NewTypeScalarType(ScalarType{Scalar: UInt64})
	}
	return Type{}
}

// FoldFromOperation builds an IR fold with a resolved direct or abstract step.
//
//golean:export
func FoldFromOperation(kind FoldKind, input Expr, seed Expr, symbol Symbol, abstract bool) Expr {
	step := foldStep(symbol, abstract)
	if kind == FoldN {
		return foldExpr(NewFoldCountFold(CountFold{Count: input, Initial: seed, Step: step}))
	}
	if kind == FoldNUntil {
		return foldExpr(NewFoldCountUntilFold(CountUntilFold{Count: input, Initial: seed, Step: step}))
	}
	if kind == FoldList {
		return foldExpr(NewFoldListFold(ListFold{Items: input, Initial: seed, Step: step}))
	}
	if kind == FoldListUntil {
		return foldExpr(NewFoldListUntilFold(ListUntilFold{Items: input, Initial: seed, Step: step}))
	}
	return Expr{}
}

func foldStep(symbol Symbol, abstract bool) FoldStep {
	if abstract {
		return NewFoldStepAbstractStep(AbstractStep{Target: symbol})
	}
	return NewFoldStepDirectStep(DirectStep{Target: symbol})
}

func foldExpr(f Fold) Expr {
	return NewExprFoldExpr(FoldExpr{Fold: f})
}

// CuratedTypeFromArguments constructs a collection or other curated Go type.
// Each argument is the already-resolved IR type in the corresponding position.
//
//golean:export
func CuratedTypeFromArguments(kind loaded.CuratedType, first Type, second Type) Type {
	if kind == loaded.CuratedArray {
		return NewTypeArrayType(ArrayType{Element: first})
	}
	if kind == loaded.CuratedBytes {
		return NewTypeByteArrayType(ByteArrayType{})
	}
	if kind == loaded.CuratedMap {
		return NewTypeMapType(MapType{Key: first, Value: second})
	}
	if kind == loaded.CuratedSet {
		return NewTypeSetType(SetType{Key: first})
	}
	if kind == loaded.CuratedOption {
		return NewTypeOptionType(OptionType{Element: first})
	}
	if kind == loaded.CuratedBitVec {
		return NewTypeBitVecType(BitVecType{})
	}
	if kind == loaded.CuratedList {
		return NewTypeListType(ListType{Element: first})
	}
	if kind == loaded.CuratedFoldControl {
		return NewTypeFoldControlType(FoldControlType{Element: first})
	}
	if kind == loaded.CuratedBox {
		return NewTypeBoxType(BoxType{Element: first})
	}
	return Type{}
}

type recursiveGroupBuild struct {
	Declarations lean.Array[Declaration]
	Members      lean.List[MutualMember]
}

func prependRecursiveMember(index uint, state recursiveGroupBuild) recursiveGroupBuild {
	item := state.Declarations.Get(state.Declarations.Size() - 1 - index).UnwrapOr(Declaration{})
	switch declaration := item.Case().(type) {
	case Struct:
		member := NewMutualMemberMutualRecord(MutualRecord{Record: declaration})
		return recursiveGroupBuild{Declarations: state.Declarations, Members: lean.Cons(member, state.Members)}
	case Enum:
		member := NewMutualMemberMutualEnum(MutualEnum{Enum: declaration})
		return recursiveGroupBuild{Declarations: state.Declarations, Members: lean.Cons(member, state.Members)}
	case MissingDeclaration:
		return state
	case Mutual:
		return state
	case TypeAlias:
		return state
	case NamedConstant:
		return state
	case Function:
		return state
	case Contract:
		return state
	}
	return state
}

// RecursiveGroupFromDeclarations builds the declaration for a validated
// component, keeping its member order.
//
//golean:export
func RecursiveGroupFromDeclarations(declarations lean.Array[Declaration]) Declaration {
	if declarations.Size() <= 1 {
		return declarations.Get(0).UnwrapOr(Declaration{})
	}
	initial := recursiveGroupBuild{Declarations: declarations, Members: lean.List[MutualMember]{}}
	group := lean.FoldN(declarations.Size(), initial, prependRecursiveMember)
	return NewDeclarationMutual(Mutual{Types: group.Members})
}
