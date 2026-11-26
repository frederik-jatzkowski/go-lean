package ir

import (
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

func typeDiagnostic() loaded.Diagnostic {
	return loaded.Diagnostic{Code: loaded.Valid, Pos: "", Detail: ""}
}

// TypeFromChecked constructs an IR type without making subset decisions.
//
//golean:export
//golean:termination:by sizeOf t
func TypeFromChecked(source loaded.Program, t loaded.CheckedType) Type {
	if t.Kind == loaded.ScalarShape {
		return ScalarFromLoaded(t.Scalar)
	}
	if t.Kind == loaded.CuratedShape {
		if t.First.IsSome() {
			if t.Second.IsSome() {
				return CuratedTypeFromArguments(t.Curated, TypeFromChecked(source, t.First.Get()), TypeFromChecked(source, t.Second.Get()))
			}
		}
		return Type{}
	}
	obj := source.ObjectOrMissing(t.Object)
	symbol := Symbol{Package: obj.Package, Name: obj.Name}
	if t.Kind == loaded.RecordShape {
		return NewTypeRecordType(RecordType{Symbol: symbol})
	}
	if t.Kind == loaded.EnumShape {
		return NewTypeEnumTypeRef(EnumTypeRef{Symbol: symbol})
	}
	return Type{}
}

type checkedFields struct {
	Source loaded.Program
	Fields lean.List[Field]
}

func lowerCheckedField(field loaded.CheckedField, state checkedFields) checkedFields {
	value := Field{Name: field.Name, Type: TypeFromChecked(state.Source, field.Type)}
	return checkedFields{Source: state.Source, Fields: lean.Cons(value, state.Fields)}
}

func prependCheckedField(field Field, fields lean.List[Field]) lean.List[Field] {
	return lean.Cons(field, fields)
}

// DeclarationFromCheckedType materializes a validated named type declaration.
//
//golean:export
func DeclarationFromCheckedType(source loaded.Program, checked loaded.CheckedTypeDeclaration) Declaration {
	obj := source.ObjectOrMissing(checked.Object)
	symbol := Symbol{Package: obj.Package, Name: obj.Name}
	reversed := lean.FoldList(checked.Fields, checkedFields{Source: source, Fields: lean.List[Field]{}}, lowerCheckedField)
	fields := lean.FoldList(reversed.Fields, lean.List[Field]{}, prependCheckedField)
	if checked.Kind == loaded.EnumShape {
		return NewDeclarationEnum(Enum{Symbol: symbol, Variants: fields, Default: checked.Default})
	}
	return NewDeclarationStruct(Struct{Symbol: symbol, Fields: fields, Recursive: checked.SelfBox})
}
