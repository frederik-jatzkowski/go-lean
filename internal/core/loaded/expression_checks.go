package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// ValidateBinaryOperands checks the subset's operand restrictions once the
// operand type has passed type validation.
//
//golean:export
func (shape CheckedType) ValidateBinaryOperands(operator string, pos string) Diagnostic {
	if shape.Kind != ScalarShape || ((operator == "+" || operator == "-") && shape.Scalar < ScalarInt8) {
		return Diagnostic{Code: UnsupportedBinaryOperands, Pos: pos, Detail: operator}
	}
	return validDiagnostic()
}

// ValidateSelector prevents reads of the generated enum's internal storage.
//
//golean:export
func (shape CheckedType) ValidateSelector(pos string) Diagnostic {
	if shape.Kind == EnumShape {
		return Diagnostic{Code: PrivateEnumStorage, Pos: pos, Detail: ""}
	}
	return validDiagnostic()
}

// ValidateBinding checks an identifier's resolved visibility.
//
//golean:export
func (id Identifier) ValidateBinding(visible bool, pos string) Diagnostic {
	if !visible {
		return Diagnostic{Code: UnknownLocalOperand, Pos: pos, Detail: id.Name}
	}
	return validDiagnostic()
}

type CompositeKind uint8

const (
	CompositeRecord CompositeKind = iota
	CompositeEmpty
	CompositeEnumZero
	CompositeFoldControl
)

type CompositeCheck struct {
	Kind       CompositeKind
	Fields     lean.Array[ObjectID]
	Diagnostic Diagnostic
}

// CheckComposite decides whether a literal is a record, a fold-control
// value, an empty curated value, or a generated enum's zero value.
//
//golean:export
func (p Program) CheckComposite(id TypeID, shape CheckedType, pos string, size uint) CompositeCheck {
	if shape.Kind == EnumShape {
		if size != 0 {
			issue := Diagnostic{Code: NonEmptyEnumLiteral, Pos: pos, Detail: ""}
			return CompositeCheck{Kind: CompositeEnumZero, Fields: lean.Array[ObjectID]{}, Diagnostic: issue}
		}
		return CompositeCheck{Kind: CompositeEnumZero, Fields: lean.Array[ObjectID]{}, Diagnostic: validDiagnostic()}
	}
	if shape.Kind == CuratedShape && shape.Curated != CuratedFoldControl && size == 0 {
		return CompositeCheck{Kind: CompositeEmpty, Fields: lean.Array[ObjectID]{}, Diagnostic: validDiagnostic()}
	}
	if shape.Kind != RecordShape && shape.Curated != CuratedFoldControl {
		issue := Diagnostic{Code: UnsupportedCompositeLiteral, Pos: pos, Detail: ""}
		return CompositeCheck{Kind: CompositeRecord, Fields: lean.Array[ObjectID]{}, Diagnostic: issue}
	}
	fields := p.Underlying(id).Fields
	if size != fields.Size() {
		issue := Diagnostic{Code: IncompleteRecordLiteral, Pos: pos, Detail: ""}
		return CompositeCheck{Kind: CompositeRecord, Fields: fields, Diagnostic: issue}
	}
	if shape.Curated == CuratedFoldControl {
		return CompositeCheck{Kind: CompositeFoldControl, Fields: fields, Diagnostic: validDiagnostic()}
	}
	return CompositeCheck{Kind: CompositeRecord, Fields: fields, Diagnostic: validDiagnostic()}
}

type KeyedElement struct {
	Value      ExprID
	Index      uint
	Found      bool
	Diagnostic Diagnostic
}

type fieldSearch struct {
	Program Program
	Fields  lean.Array[ObjectID]
	Name    string
	Index   uint
}

func findFieldIndex(index uint, search fieldSearch) lean.FoldControl[fieldSearch] {
	field := search.Program.ObjectOrMissing(search.Fields.Get(index).UnwrapOr(0))
	if field.Name == search.Name {
		found := fieldSearch{Program: search.Program, Fields: search.Fields, Name: search.Name, Index: index}
		return lean.FoldControl[fieldSearch]{State: found, Stop: true}
	}
	return lean.FoldControl[fieldSearch]{State: search, Stop: false}
}

func rejectUnkeyed(pos string) KeyedElement {
	issue := Diagnostic{Code: UnkeyedRecordLiteral, Pos: pos, Detail: ""}
	return KeyedElement{Value: 0, Index: 0, Found: false, Diagnostic: issue}
}

// CheckKeyedElement resolves one explicitly keyed field in source order.
//
//golean:export
func (p Program) CheckKeyedElement(id ExprID, fields lean.Array[ObjectID]) KeyedElement {
	e := p.ExpressionOrMissing(id)
	switch form := e.Form.Case().(type) {
	case KeyedExpr:
		search := fieldSearch{Program: p, Fields: fields, Name: form.Name, Index: 0}
		resolved := lean.FoldNUntil(fields.Size(), search, findFieldIndex)
		return KeyedElement{Value: form.Value, Index: resolved.State.Index, Found: resolved.Stop, Diagnostic: validDiagnostic()}
	case UnsupportedExpr:
		return rejectUnkeyed(e.Pos)
	case Parenthesized:
		return rejectUnkeyed(e.Pos)
	case Identifier:
		return rejectUnkeyed(e.Pos)
	case UnaryExpr:
		return rejectUnkeyed(e.Pos)
	case BinaryExpr:
		return rejectUnkeyed(e.Pos)
	case SelectorExpr:
		return rejectUnkeyed(e.Pos)
	case CompositeExpr:
		return rejectUnkeyed(e.Pos)
	case CallExpr:
		return rejectUnkeyed(e.Pos)
	}
	return rejectUnkeyed(e.Pos)
}

// CheckConversion checks the operand count and type identity of a dynamic cast.
//
//golean:export
func (p Program) CheckConversion(e Expression, call CallExpr) Diagnostic {
	if call.Args.Size() == 1 {
		operand := p.ExpressionOrMissing(call.Args.Get(0).UnwrapOr(0))
		if p.Underlying(e.Type).AllowsIdentityConversion(p.Underlying(operand.Type)) {
			return validDiagnostic()
		}
	}
	return Diagnostic{Code: InvalidCallTarget, Pos: e.Pos, Detail: ""}
}
