// Package ir represents pure, typed expressions and returning control flow.
package ir

import "strconv"

type Program struct {
	Functions []Function
	WordBits  int64
}

type Function struct {
	Symbol     Symbol
	TypeParams []Type
	Params     []Binder
	Result     Type
	Body       Body
	CanPanic   bool
}

type Symbol struct {
	Package    string
	File       string
	Name       string
	Dependency string
}

type Binder struct {
	Name  string
	Index int
	Type  Type
}

type Type string

const (
	Int8     Type = "Int8"
	Int16    Type = "Int16"
	Int32    Type = "Int32"
	Int64    Type = "Int64"
	UInt8    Type = "UInt8"
	UInt16   Type = "UInt16"
	UInt32   Type = "UInt32"
	UInt64   Type = "UInt64"
	IntWord  Type = "int"
	UIntWord Type = "uint"
	Bool     Type = "Bool"
	Bytes    Type = "ByteArray"
	Float32  Type = "Float32"
	Float64  Type = "Float"
)

func (t Type) IsInteger() bool {
	return t == Int8 || t == Int16 || t == Int32 || t == Int64 || t == IntWord || t.IsUnsigned()
}

func (t Type) IsUnsigned() bool {
	return t == UInt8 || t == UInt16 || t == UInt32 || t == UInt64 || t == UIntWord
}

func (t Type) IsWord() bool { return t == IntWord || t == UIntWord }

func TypeParameter(index int) Type { return Type("α" + strconv.Itoa(index)) }

// Body introduces immutable bindings and ends in a return or a returning branch.
type Body struct {
	Bindings []Binding
	Result   Result
}

type Binding struct {
	Binder   Binder
	Value    Expr
	CanPanic bool
}

type Result interface{ result() }

type Return struct{ Value Expr }

type If struct {
	Condition Expr
	Then      Body
	Else      Body
}

func (Return) result() {}
func (If) result()     {}

type Expr interface{ expr() }

type IntLiteral struct {
	Value string
	Type  Type
}

type BoolLiteral bool
type BytesLiteral string
type Float32Literal uint32
type Float64Literal uint64
type Ref Binder
type Negate struct{ Value Expr }
type Not struct{ Value Expr }
type ByteLen struct{ Value Expr }

type Convert struct {
	Value Expr
	To    Type
}

type Call struct {
	Callee Symbol
	Args   []Expr
}

type Binary struct {
	Op          Operator
	Left, Right Expr
	OperandType Type
}

func (IntLiteral) expr()     {}
func (BoolLiteral) expr()    {}
func (BytesLiteral) expr()   {}
func (Float32Literal) expr() {}
func (Float64Literal) expr() {}
func (Ref) expr()            {}
func (Negate) expr()         {}
func (Not) expr()            {}
func (ByteLen) expr()        {}
func (Convert) expr()        {}
func (Binary) expr()         {}
func (Call) expr()           {}

type Operator int

const (
	Add Operator = iota
	Subtract
	Multiply
	Divide
	Equal
	NotEqual
	Less
	LessEqual
	Greater
	GreaterEqual
)
