package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// LookupObject resolves an object ID in this program.
//
//golean:export
func (p Program) LookupObject(id ObjectID) lean.Option[Object] {
	if id == 0 {
		return lean.None[Object]()
	}
	return p.Objects.Get(uint(id))
}

// LookupType resolves a type ID in this program.
//
//golean:export
func (p Program) LookupType(id TypeID) lean.Option[Type] {
	if id == 0 {
		return lean.None[Type]()
	}
	return p.Types.Get(uint(id))
}

// LookupExpression resolves an expression ID in this program.
//
//golean:export
func (p Program) LookupExpression(id ExprID) lean.Option[Expression] {
	if id == 0 {
		return lean.None[Expression]()
	}
	return p.Expressions.Get(uint(id))
}

// LookupStatement resolves a statement ID in this program.
//
//golean:export
func (p Program) LookupStatement(id StmtID) lean.Option[Statement] {
	if id == 0 {
		return lean.None[Statement]()
	}
	return p.Statements.Get(uint(id))
}
