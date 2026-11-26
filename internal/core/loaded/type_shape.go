package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type TypeShapeKind uint8

const (
	UnsupportedShape TypeShapeKind = iota
	ScalarShape
	CuratedShape
	EnumShape
	RecordShape
)

type CuratedType uint8

const (
	UnknownCuratedType CuratedType = iota
	CuratedArray
	CuratedBytes
	CuratedMap
	CuratedSet
	CuratedBox
	CuratedOption
	CuratedBitVec
	CuratedList
	CuratedFoldControl
)

type TypeShape struct {
	Kind       TypeShapeKind
	Scalar     ScalarKind
	Curated    CuratedType
	Object     ObjectID
	Arguments  lean.Array[TypeID]
	Fields     lean.Array[ObjectID]
	Diagnostic Diagnostic
}

func classifyCuratedType(name string) CuratedType {
	if name == "Array" {
		return CuratedArray
	}
	if name == "ByteArray" {
		return CuratedBytes
	}
	if name == "OrderedMap" {
		return CuratedMap
	}
	if name == "OrderedSet" {
		return CuratedSet
	}
	if name == "Box" {
		return CuratedBox
	}
	if name == "Option" {
		return CuratedOption
	}
	if name == "BitVec" {
		return CuratedBitVec
	}
	if name == "List" {
		return CuratedList
	}
	if name == "FoldControl" {
		return CuratedFoldControl
	}
	return UnknownCuratedType
}

func unsupportedShape(issue Diagnostic) TypeShape {
	return TypeShape{Kind: UnsupportedShape, Scalar: NotScalar, Curated: UnknownCuratedType, Object: 0,
		Arguments: lean.Array[TypeID]{}, Fields: lean.Array[ObjectID]{}, Diagnostic: issue}
}

func scalarShape(t Type, wordBits int, pos string) TypeShape {
	scalar := t.Scalar(wordBits)
	if scalar == NotScalar {
		return unsupportedShape(Diagnostic{Code: UnsupportedScalarType, Pos: pos, Detail: t.Display})
	}
	return TypeShape{Kind: ScalarShape, Scalar: scalar, Curated: UnknownCuratedType, Object: 0,
		Arguments: lean.Array[TypeID]{}, Fields: lean.Array[ObjectID]{}, Diagnostic: validDiagnostic()}
}

// ClassifyType resolves aliases and checks the outer type before its
// children or dependencies are visited.
//
//golean:export
func (p Program) ClassifyType(id TypeID, wordBits int, pos string) TypeShape {
	original := p.LookupType(id).UnwrapOr(emptyLoadedType())
	declared := p.LookupObject(original.Object).UnwrapOr(emptyLoadedObject())
	if declared.Issue != "" {
		return unsupportedShape(Diagnostic{Code: LoadedTypeIssue, Pos: "", Detail: declared.Issue})
	}
	t := p.Unalias(id)
	if t.Kind == BasicType {
		return scalarShape(t, wordBits, pos)
	}
	if t.Kind == NamedType {
		return p.classifyNamed(original.Display, t, wordBits, pos)
	}
	return unsupportedShape(Diagnostic{Code: UnsupportedGoType, Pos: pos, Detail: original.Display})
}

func (p Program) classifyNamed(display string, t Type, wordBits int, pos string) TypeShape {
	obj := p.LookupObject(t.Object).UnwrapOr(emptyLoadedObject())
	if obj.Issue != "" {
		return unsupportedShape(Diagnostic{Code: LoadedTypeIssue, Pos: "", Detail: obj.Issue})
	}
	if obj.Package == Curated {
		kind := classifyCuratedType(obj.Name)
		if kind != UnknownCuratedType {
			return TypeShape{Kind: CuratedShape, Scalar: NotScalar, Curated: kind, Object: t.Object,
				Arguments: t.Args, Fields: lean.Array[ObjectID]{}, Diagnostic: validDiagnostic()}
		}
		return unsupportedShape(Diagnostic{Code: UnsupportedGoType, Pos: pos, Detail: display})
	}
	if t.Generic {
		return unsupportedShape(Diagnostic{Code: UnsupportedGoType, Pos: pos, Detail: display})
	}
	if obj.Enum.IsSome() {
		return TypeShape{Kind: EnumShape, Scalar: NotScalar, Curated: UnknownCuratedType, Object: t.Object,
			Arguments: lean.Array[TypeID]{}, Fields: lean.Array[ObjectID]{}, Diagnostic: validDiagnostic()}
	}
	underlying := p.LookupType(t.Underlying).UnwrapOr(emptyLoadedType())
	if underlying.Kind == BasicType {
		return scalarShape(underlying, wordBits, pos)
	}
	if underlying.Kind == StructType && t.PackageScope {
		return TypeShape{Kind: RecordShape, Scalar: NotScalar, Curated: UnknownCuratedType, Object: t.Object,
			Arguments: lean.Array[TypeID]{}, Fields: underlying.Fields, Diagnostic: validDiagnostic()}
	}
	return unsupportedShape(Diagnostic{Code: UnsupportedGoType, Pos: pos, Detail: display})
}

// ValidateField checks the Go field shape required for a modeled record.
//
//golean:export
func (o Object) ValidateField() Diagnostic {
	if o.Embedded || o.Name == "_" {
		return Diagnostic{Code: UnsupportedRecordField, Pos: o.Pos, Detail: ""}
	}
	return validDiagnostic()
}
