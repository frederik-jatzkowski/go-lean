// Package ir represents pure, typed expressions and returning control flow.
package ir

import (
	"strconv"
	"strings"
)

type Program struct {
	Functions []Function
	Records   map[Type]Record
	WordBits  int64
}

type Record struct {
	Symbol Symbol
	Fields []Field
}

type Field struct {
	Name string
	Type Type
}

type Function struct {
	Symbol     Symbol
	TypeParams []Type
	Params     []Binder
	Result     Type
	Body       Body
	CanPanic   bool
	Loop       *CountedLoop
}

// CountedLoop repeats the SSA update once per unit of natural-number fuel.
type CountedLoop struct {
	Symbol Symbol
	Params []Binder
	State  Binder
	Steps  []Binding
	Next   Expr
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

func UnaryFunctionType(input, output Type) Type { return Type("func:" + input + "\x00" + output) }

func (t Type) UnaryFunctionShape() (input, output Type) {
	if signature, ok := strings.CutPrefix(string(t), "func:"); ok {
		input, output, _ := strings.Cut(signature, "\x00")
		return Type(input), Type(output)
	}
	return "", ""
}

func RecordType(pkg, name string) Type { return Type("struct:" + pkg + "." + name) }

func (t Type) IsRecord() bool { return strings.HasPrefix(string(t), "struct:") }

func RecordPointer(pointee Type) Type { return Type("pointer:" + string(pointee)) }

func (t Type) Pointee() Type {
	if pointee, ok := strings.CutPrefix(string(t), "pointer:"); ok {
		return Type(pointee)
	}
	return ""
}

func SliceType(elem Type) Type { return Type("slice:" + string(elem)) }

func (t Type) SliceElem() Type {
	if elem, ok := strings.CutPrefix(string(t), "slice:"); ok {
		return Type(elem)
	}
	return ""
}

func MapType(key, value Type) Type { return Type("map:" + key + ":" + value) }

func (t Type) MapShape() (key, value Type) {
	if entries, ok := strings.CutPrefix(string(t), "map:"); ok {
		key, value, _ := strings.Cut(entries, ":")
		return Type(key), Type(value)
	}
	return "", ""
}

func OptionType(elem Type) Type { return Type("option:" + elem) }

func (t Type) OptionElem() Type {
	if elem, ok := strings.CutPrefix(string(t), "option:"); ok {
		return Type(elem)
	}
	return ""
}

func ArrayType(elem Type, length int64) Type {
	return Type("array:" + strconv.FormatInt(length, 10) + ":" + string(elem))
}

func (t Type) ArrayShape() (elem Type, length string) {
	shape, ok := strings.CutPrefix(string(t), "array:")
	if !ok {
		return "", ""
	}
	length, element, _ := strings.Cut(shape, ":")
	return Type(element), length
}

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

type ListFold struct {
	Sequence Expr
	Initial  Expr
	State    Binder
	Element  Binder
	Steps    []Binding
	Next     Expr
}

type ListBuild struct {
	Sequence Expr
	Element  Binder
	Steps    []Binding
	Next     Expr
}

func (Return) result()    {}
func (If) result()        {}
func (ListFold) result()  {}
func (ListBuild) result() {}

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
type ToNat struct{ Value Expr }

type RecordLiteral struct {
	Type   Type
	Values []Expr
}

type RecordField struct {
	Value Expr
	Name  string
}

type CheckedRecordField struct {
	Value Expr
	Type  Type
	Name  string
}

type NilPointer struct{}
type EmptySlice struct{}
type EmptyMap struct{}

type MapLookup struct {
	Map Expr
	Key Expr
}

type MapUpdate struct {
	Map   Expr
	Key   Expr
	Value Expr
}

type OptionGetD struct {
	Value   Expr
	Default Expr
}

type OptionIsSome struct{ Value Expr }

type CheckedIndex struct {
	Sequence     Expr
	SequenceType Type
	Index        Expr
	IndexType    Type
}

type Convert struct {
	Value Expr
	To    Type
}

type Call struct {
	Callee Symbol
	Args   []Expr
}

type FunctionRef Symbol

type Apply struct {
	Function Expr
	Argument Expr
}

type Binary struct {
	Op          Operator
	Left, Right Expr
	OperandType Type
}

func (IntLiteral) expr()         {}
func (BoolLiteral) expr()        {}
func (BytesLiteral) expr()       {}
func (Float32Literal) expr()     {}
func (Float64Literal) expr()     {}
func (Ref) expr()                {}
func (Negate) expr()             {}
func (Not) expr()                {}
func (ByteLen) expr()            {}
func (ToNat) expr()              {}
func (RecordLiteral) expr()      {}
func (RecordField) expr()        {}
func (CheckedRecordField) expr() {}
func (NilPointer) expr()         {}
func (EmptySlice) expr()         {}
func (EmptyMap) expr()           {}
func (MapLookup) expr()          {}
func (MapUpdate) expr()          {}
func (OptionGetD) expr()         {}
func (OptionIsSome) expr()       {}
func (CheckedIndex) expr()       {}
func (Convert) expr()            {}
func (Binary) expr()             {}
func (Call) expr()               {}
func (FunctionRef) expr()        {}
func (Apply) expr()              {}

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
