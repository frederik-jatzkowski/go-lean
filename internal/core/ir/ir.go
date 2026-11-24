// Package ir defines the closed, typed representation consumed by Lean emission.
//
//golean:generate:enum Type { MissingType default, ScalarType, RecordType, EnumTypeRef, ArrayType, ByteArrayType, MapType, SetType, OptionType, BitVecType, ListType, FoldControlType, BoxType }
//golean:generate:enum Expr { MissingExpr default, Constant, Local, Let, If, Join, Jump, Unary, Binary, FieldRead, FoldStateRead, FoldStopRead, StructLiteral, Constructor, Match, Call, AbstractCall, PrimitiveExpr, FoldExpr, FoldControlLiteral }
//golean:generate:enum Declaration { MissingDeclaration default, Struct, Enum, Mutual, TypeAlias, NamedConstant, Function, Contract }
//golean:generate:enum MutualMember { MutualRecord default, MutualEnum }
//golean:generate:enum Primitive { MissingPrimitive default, EmptyValue, MakeSome, MakeNone, ListNil, ListCons, ListIsEmpty, OptionIsSome, OptionUnwrapOr, BoxRead, ArrayPush, ByteArrayPush, ArrayPop, ArrayGet, ByteArrayGet, BitVecGet, ArraySet, ByteArraySet, BitVecSet, CollectionSize, ByteArrayExtract, MapFind, MapContains, MapInsert, MapErase, SetContains, SetInsert, SetErase, MakeBitVec, BitVecWidth, BitVecToUint64 }
//golean:generate:enum Fold { CountFold default, CountUntilFold, ListFold, ListUntilFold }
//golean:generate:enum FoldStep { DirectStep default, AbstractStep }
//golean:verify emptyValueKeepsType : ∀ t : «Type»,
//golean:verify+ NewEmptyValueExpr t = Expr.PrimitiveExpr (PrimitiveExpr.mk (Primitive.EmptyValue (EmptyValue.mk t)))
//golean:verify countedFoldKeepsDirectStep : ∀ (count seed : Expr) (target : Symbol),
//golean:verify+ FoldFromOperation FoldN count seed target false =
//golean:verify+ Expr.FoldExpr (FoldExpr.mk (Fold.CountFold (CountFold.mk count seed (FoldStep.DirectStep (DirectStep.mk target)))))
//golean:verify listFoldUntilKeepsAbstractStep : ∀ (items seed : Expr) (target : Symbol),
//golean:verify+ FoldFromOperation FoldListUntil items seed target true =
//golean:verify+ Expr.FoldExpr (FoldExpr.mk (Fold.ListUntilFold (ListUntilFold.mk items seed (FoldStep.AbstractStep (AbstractStep.mk target)))))
package ir

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type Symbol struct {
	Package string
	Name    string
}

type Kind uint8

const (
	Bool Kind = iota + 1
	String
	Int8
	Int16
	Int32
	Int64
	UInt8
	UInt16
	UInt32
	UInt64
	Record
	Array
	ByteArray
	OrderedMap
	OrderedSet
	Option
	BitVec
	List
	FoldControl
	Box
	EnumType
)

type MissingType struct{}
type ScalarType struct{ Scalar Kind }
type RecordType struct{ Symbol Symbol }
type EnumTypeRef struct{ Symbol Symbol }
type ArrayType struct{ Element Type }
type ByteArrayType struct{}
type MapType struct{ Key, Value Type }
type SetType struct{ Key Type }
type OptionType struct{ Element Type }
type BitVecType struct{}
type ListType struct{ Element Type }
type FoldControlType struct{ Element Type }
type BoxType struct{ Element Type }

type Field struct {
	Name string
	Type Type
}

type Struct struct {
	Symbol    Symbol
	Fields    lean.List[Field]
	Recursive bool
}

type Enum struct {
	Symbol   Symbol
	Variants lean.List[Field]
	Default  int
}

type Mutual struct{ Types lean.List[MutualMember] }

type TypeAlias struct {
	Symbol Symbol
	Type   Type
}

type NamedConstant struct {
	Symbol Symbol
	Value  Constant
}

type Binding struct {
	Unused bool
	Name   string
	ID     int
	Type   Type
}

type Function struct {
	Symbol      Symbol
	Params      lean.List[Binding]
	Result      Type
	Body        Expr
	Contracts   lean.List[Symbol]
	Termination string
}

type Proposition struct {
	Name string
	Lean string
}

type Contract struct {
	Caller, Callee Symbol
	Params         lean.List[Type]
	Result         Type
	Assumptions    lean.List[Proposition]
}

type Law struct {
	Proposition Proposition
	Caller      Symbol
	Contracts   lean.List[Symbol]
}

type Package struct {
	Path, Name, Dir string
	Word            Kind
	Imports         lean.List[string]
	LeanImports     lean.List[string]
	Decls           lean.List[Declaration]
	Laws            lean.List[Law]
	Folds           FoldKind
}

type Constant struct {
	Type Type
	// Value is decimal for integers, true/false for booleans, and raw bytes for strings.
	Value string
}

type Local struct{ ID int }
type Let struct {
	ID          int
	Value, Body Expr
}
type If struct{ Cond, Then, Else Expr }

// Join binds the continuation of an if whose branches can both fall through.
type Join struct {
	ID         int
	Next, Body Expr
}

type Jump struct{ ID int }

type UnaryOp uint8

const Not UnaryOp = iota + 1

type Unary struct {
	Op    UnaryOp
	Value Expr
}

type BinaryOp uint8

const (
	Add BinaryOp = iota + 1
	Sub
	Eq
	Ne
	Lt
	Le
	Gt
	Ge
	And
	Or
)

type Binary struct {
	Op          BinaryOp
	Kind        Kind
	Left, Right Expr
}
type FieldRead struct {
	Record Expr
	Name   string
}
type StructLiteral struct {
	Type   Symbol
	Fields ExprSeq
}
type Constructor struct {
	Enum    Symbol
	Variant string
	Value   Expr
}

type MatchCase struct {
	Variant string
	Binding int
	Body    Expr
}
type Match struct {
	Value Expr
	Cases MatchSeq
}

type Call struct {
	Target Symbol
	Args   ExprSeq
}
type AbstractCall struct {
	Target Symbol
	Args   ExprSeq
}

type FoldKind uint8

const (
	FoldN FoldKind = 1 << iota
	FoldNUntil
	FoldList
	FoldListUntil
)

type CountFold struct {
	Count, Initial Expr
	Step           FoldStep
}
type CountUntilFold struct {
	Count, Initial Expr
	Step           FoldStep
}
type ListFold struct {
	Items, Initial Expr
	Step           FoldStep
}
type ListUntilFold struct {
	Items, Initial Expr
	Step           FoldStep
}
type DirectStep struct{ Target Symbol }
type AbstractStep struct{ Target Symbol }
type FoldExpr struct{ Fold Fold }

type FoldControlLiteral struct {
	State, Stop Expr
}

type PrimitiveExpr struct{ Primitive Primitive }
type MissingPrimitive struct{}
type EmptyValue struct{ Type Type }
type MakeSome struct{ Value Expr }
type MakeNone struct{ Type Type }
type ListNil struct{ Type Type }
type ListCons struct{ Head, Tail Expr }
type ListIsEmpty struct{ Items Expr }
type OptionIsSome struct{ Option Expr }
type OptionUnwrapOr struct{ Option, Fallback Expr }
type BoxRead struct{ Box, Fallback Expr }
type ArrayPush struct{ Array, Value Expr }
type ByteArrayPush struct{ Bytes, Value Expr }
type ArrayPop struct{ Array Expr }
type ArrayGet struct{ Array, Index Expr }
type ByteArrayGet struct{ Bytes, Index Expr }
type BitVecGet struct{ Bits, Index Expr }
type ArraySet struct{ Array, Index, Value Expr }
type ByteArraySet struct{ Bytes, Index, Value Expr }
type BitVecSet struct {
	Type               Type
	Bits, Index, Value Expr
}
type CollectionSize struct{ Collection Expr }
type ByteArrayExtract struct{ Bytes, Start, End Expr }
type MapFind struct{ Map, Key Expr }
type MapContains struct{ Map, Key Expr }
type MapInsert struct{ Map, Key, Value Expr }
type MapErase struct{ Map, Key Expr }
type SetContains struct{ Set, Key Expr }
type SetInsert struct{ Set, Key Expr }
type SetErase struct{ Set, Key Expr }
type MakeBitVec struct{ Width, Value Expr }
type BitVecWidth struct{ Bits Expr }
type BitVecToUint64 struct{ Bits Expr }

// Kind classifies the type for lowering and emission.
//
//golean:export
func (t Type) Kind() Kind {
	switch v := t.Case().(type) {
	case MissingType:
		return 0
	case ScalarType:
		return v.Scalar
	case RecordType:
		return Record
	case EnumTypeRef:
		return EnumType
	case ArrayType:
		return Array
	case ByteArrayType:
		return ByteArray
	case MapType:
		return OrderedMap
	case SetType:
		return OrderedSet
	case OptionType:
		return Option
	case BitVecType:
		return BitVec
	case ListType:
		return List
	case FoldControlType:
		return FoldControl
	case BoxType:
		return Box
	}
	return 0
}

type MutualRecord struct{ Record Struct }
type MutualEnum struct{ Enum Enum }
type MissingExpr struct{}
type MissingDeclaration struct{}
type FoldStateRead struct{ Control Expr }
type FoldStopRead struct{ Control Expr }

// ExprSeq stores ordered expression children. An empty box ends the sequence.
type ExprSeq struct{ First lean.Box[ExprSeqItem] }
type ExprSeqItem struct {
	Value Expr
	Rest  ExprSeq
}

// MatchSeq stores match arms in source order. An empty box ends the sequence.
type MatchSeq struct{ First lean.Box[MatchSeqItem] }
type MatchSeqItem struct {
	Value MatchCase
	Rest  MatchSeq
}
