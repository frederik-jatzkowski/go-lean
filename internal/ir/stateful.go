package ir

const (
	Nat  Type = "Nat"
	Unit Type = "Unit"
)

type UnitLiteral struct{}
type Some struct{ Value Expr }
type Pair struct{ Left, Right Expr }
type PairField struct {
	Value  Expr
	Second bool
}
type RecordUpdate struct {
	Record Expr
	Field  string
	Value  Expr
}
type ListLength struct{ List Expr }
type SliceLength struct{ List Expr }
type Cons struct{ Head, Tail Expr }
type Reverse struct{ List Expr }
type IndexFuel struct{ Length, Cursor Expr }
type WithReceiver struct {
	Receiver Expr
	State    Binder
	Body     Body
}
type TailCall struct {
	Call      Call
	Recursive bool
}

func (UnitLiteral) expr()    {}
func (Some) expr()           {}
func (Pair) expr()           {}
func (PairField) expr()      {}
func (RecordUpdate) expr()   {}
func (ListLength) expr()     {}
func (SliceLength) expr()    {}
func (Cons) expr()           {}
func (Reverse) expr()        {}
func (IndexFuel) expr()      {}
func (TailCall) result()     {}
func (WithReceiver) result() {}
