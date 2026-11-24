// Package loaded represents the type-checked Go input to lowering.
//
//golean:generate:enum ExprForm { UnsupportedExpr default, Parenthesized, Identifier, UnaryExpr, BinaryExpr, SelectorExpr, CompositeExpr, KeyedExpr, CallExpr }
//golean:generate:enum StmtForm { UnsupportedStmt default, ReturnStmt, IfStmt, SwitchStmt, LoopStmt, ShortDecl, VarDecl }
package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

const Curated = "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// IDs are local to a Program. Zero denotes an absent reference.
type ObjectID uint
type TypeID uint
type ExprID uint
type StmtID uint

type Program struct {
	SelectedPackages lean.Array[string]
	Packages         lean.OrderedMap[string, Package]
	Objects          lean.Array[Object]
	Types            lean.Array[Type]
	Expressions      lean.Array[Expression]
	Statements       lean.Array[Statement]
}

type Package struct {
	Path, Name, Dir, Module string
	WordBits                int
	Modeled                 bool
	Issue                   string
	Declarations            lean.Array[Declaration]
	Laws                    lean.Array[Proposition]
	LeanImports             lean.Array[string]
}

type Declaration struct {
	Pos    string
	Object ObjectID
}

type Function struct {
	Body                      lean.Array[StmtID]
	HasBody, Export, Selected bool
	Pos, Termination, Issue   string
	Laws, Assumptions         lean.Array[Proposition]
	LawPositions              lean.Array[string]
	Abstract                  lean.Array[AbstractCallee]
}

type AbstractCallee struct {
	Name   string
	Object ObjectID
}

type Enum struct {
	Payloads lean.Array[ObjectID]
	Default  string
}

type EnumConstructor struct {
	Owner   ObjectID
	Variant string
}

type ObjectKind uint8

const (
	UnknownObject ObjectKind = iota
	FunctionObject
	TypeName
	ConstantObject
	Variable
)

type Object struct {
	Kind                                ObjectKind
	Embedded                            bool
	Name, Package, FullName, Pos, Issue string
	Type, DefaultType                   TypeID
	Value                               Constant
	Function                            lean.Option[Function]
	Enum                                lean.Option[Enum]
	Constructor                         lean.Option[EnumConstructor]
	EnumCase                            ObjectID
}

type Constant struct {
	Present, Integer, Negative bool
	MagnitudeBits, SignedBits  int
	Value                      string
}
type TypeKind uint8

const (
	UnsupportedType TypeKind = iota
	BasicType
	NamedType
	AliasType
	StructType
	SignatureType
)

type Type struct {
	Kind                                           TypeKind
	Display, Basic                                 string
	Object, Receiver                               ObjectID
	Underlying                                     TypeID
	Args                                           lean.Array[TypeID]
	Fields, Params, Results                        lean.Array[ObjectID]
	Generic, Variadic, PackageScope, ValueReceiver bool
}

type SelectionKind uint8

const (
	NoSelection SelectionKind = iota
	FieldValue
	MethodValue
	MethodExpression
)

type Selection struct {
	Kind     SelectionKind
	Receiver TypeID
	Object   ObjectID
	Direct   bool
}

type Expression struct {
	Pos, Syntax string
	Type        TypeID
	Constant    Constant
	Form        ExprForm
}

type UnsupportedExpr struct{}
type Parenthesized struct{ Inner ExprID }
type Identifier struct {
	Name   string
	Object ObjectID
}

type UnaryExpr struct {
	Operator string
	Operand  ExprID
}

type BinaryExpr struct {
	Operator    string
	Left, Right ExprID
}

type SelectorExpr struct {
	Base      ExprID
	Object    ObjectID
	Selection Selection
}

type CompositeExpr struct{ Elements lean.Array[ExprID] }
type KeyedExpr struct {
	Name  string
	Value ExprID
}

type CallExpr struct {
	Object               ObjectID
	Receiver             ExprID
	Args                 lean.Array[ExprID]
	Selection            Selection
	Ellipsis, Conversion bool
}

type Statement struct {
	Pos  string
	Form StmtForm
}

type UnsupportedStmt struct{ Syntax string }
type ReturnStmt struct{ Values lean.Array[ExprID] }
type IfStmt struct {
	HasInitializer bool
	Condition      ExprID
	Then, Else     lean.Array[StmtID]
}

type SwitchStmt struct {
	Receiver   ExprID
	CaseMethod ObjectID
	Cases      lean.Array[SwitchClause]
}

type LoopStmt struct{}
type ShortDecl struct {
	ValidForm bool
	Names     lean.Array[Binding]
	Values    lean.Array[ExprID]
}

type VarDecl struct {
	ValidForm   bool
	Names       lean.Array[Binding]
	Values      lean.Array[ExprID]
	ZeroType    TypeID
	ZeroTypePos string
}

type Binding struct {
	Pos        string
	Object     ObjectID
	Identifier bool
}

type SwitchClause struct {
	Pos              string
	Count            int
	Variant, Binding ObjectID
	Body             lean.Array[StmtID]
}

// Proposition records a Lean proposition as written in a Go directive.
type Proposition struct {
	Name, Lean string
}
