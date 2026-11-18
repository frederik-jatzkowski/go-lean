// Package ir represents pure, typed expressions and returning control flow.
package ir

type Program struct {
	Functions []Function
}

type Function struct {
	Symbol   Symbol
	Params   []Binder
	Body     Body
	CanPanic bool
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

func (Return) result() {}
func (If) result()     {}

type Expr interface{ expr() }

type IntLiteral string
type BoolLiteral bool
type Ref Binder
type Negate struct{ Value Expr }

type Call struct {
	Callee Symbol
	Args   []Expr
}

type Binary struct {
	Op          Operator
	Left, Right Expr
}

func (IntLiteral) expr()  {}
func (BoolLiteral) expr() {}
func (Ref) expr()         {}
func (Negate) expr()      {}
func (Binary) expr()      {}
func (Call) expr()        {}

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
