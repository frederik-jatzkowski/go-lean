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

func emptyLoadedType() Type {
	return Type{Kind: UnsupportedType, Display: "", Basic: "", Object: 0, Receiver: 0, Underlying: 0,
		Args: lean.Array[TypeID]{}, Fields: lean.Array[ObjectID]{}, Params: lean.Array[ObjectID]{}, Results: lean.Array[ObjectID]{},
		Generic: false, Variadic: false, PackageScope: false, ValueReceiver: false}
}

func emptyLoadedObject() Object {
	return Object{Kind: UnknownObject, Embedded: false, Name: "", ModelName: "", Package: "", FullName: "", Pos: "", Issue: "",
		Type: 0, DefaultType: 0, Value: Constant{Present: false, Integer: false, Negative: false, MagnitudeBits: 0, SignedBits: 0, Value: ""},
		Function: lean.None[Function](), Enum: lean.None[Enum](), Constructor: lean.None[EnumConstructor](), EnumCase: 0}
}

// Unalias resolves a type through its flattened alias target.
//
//golean:export
func (p Program) Unalias(id TypeID) Type {
	t := p.LookupType(id).UnwrapOr(emptyLoadedType())
	if t.Kind == AliasType {
		return p.LookupType(t.Underlying).UnwrapOr(emptyLoadedType())
	}
	return t
}

// Underlying resolves aliases and removes the named type wrapper.
//
//golean:export
func (p Program) Underlying(id TypeID) Type {
	t := p.Unalias(id)
	if t.Kind == NamedType {
		return p.LookupType(t.Underlying).UnwrapOr(emptyLoadedType())
	}
	return t
}

// IsSelfBox identifies a direct boxed reference back to the enclosing record.
//
//golean:export
func (p Program) IsSelfBox(id TypeID, owner ObjectID) bool {
	box := p.Unalias(id)
	obj := p.LookupObject(box.Object).UnwrapOr(emptyLoadedObject())
	if box.Kind != NamedType || obj.Package != Curated || obj.Name != "Box" {
		return false
	}
	payload := p.Unalias(box.Args.Get(0).UnwrapOr(0))
	return payload.Kind == NamedType && payload.Object == owner
}

// ObjectOrMissing supplies the missing object sentinel for unchecked IDs.
//
//golean:export
func (p Program) ObjectOrMissing(id ObjectID) Object {
	return p.LookupObject(id).UnwrapOr(emptyLoadedObject())
}

// PackageOrMissing supplies an empty package when a path is unresolved.
//
//golean:export
func (p Program) PackageOrMissing(path string) Package {
	missing := Package{Path: "", Name: "", Dir: "", Module: "", WordBits: 0, Modeled: false, Issue: "",
		Declarations: lean.Array[Declaration]{}, Laws: lean.Array[Proposition]{}, LeanImports: lean.Array[string]{}}
	return p.Packages.Find(path).UnwrapOr(missing)
}

// ExpressionOrMissing supplies a sentinel if no loaded expression has this ID.
//
//golean:export
func (p Program) ExpressionOrMissing(id ExprID) Expression {
	missing := Expression{Pos: "", Syntax: "", Type: 0,
		Constant: Constant{Present: false, Integer: false, Negative: false, MagnitudeBits: 0, SignedBits: 0, Value: ""},
		Form:     NewExprFormUnsupportedExpr(UnsupportedExpr{})}
	return p.LookupExpression(id).UnwrapOr(missing)
}

// TypeOrMissing supplies the missing type sentinel for unchecked IDs.
//
//golean:export
func (p Program) TypeOrMissing(id TypeID) Type {
	return p.LookupType(id).UnwrapOr(emptyLoadedType())
}
