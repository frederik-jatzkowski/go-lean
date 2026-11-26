package loaded

import (
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

// CheckedType is a type that passed subset checking. Named types refer to
// their declarations by identity and curated types carry checked arguments.
type CheckedType struct {
	Kind          TypeShapeKind
	Scalar        ScalarKind
	Curated       CuratedType
	Object        ObjectID
	First, Second lean.Box[CheckedType]
}

type CheckedField struct {
	Name string
	Type CheckedType
}

type CheckedTypeDeclaration struct {
	Kind    TypeShapeKind
	Object  ObjectID
	Fields  lean.List[CheckedField]
	Default int
	SelfBox bool
}

type TypeEvent struct {
	Package, Dependency string
	Declaration         lean.Option[CheckedTypeDeclaration]
}

func noCheckedType() CheckedType {
	return CheckedType{Kind: UnsupportedShape, Scalar: NotScalar, Curated: UnknownCuratedType, Object: 0,
		First: lean.Box[CheckedType]{}, Second: lean.Box[CheckedType]{}}
}

func checkedScalar(kind ScalarKind) CheckedType {
	return CheckedType{Kind: ScalarShape, Scalar: kind, Curated: UnknownCuratedType, Object: 0,
		First: lean.Box[CheckedType]{}, Second: lean.Box[CheckedType]{}}
}

func checkedCurated(kind CuratedType, first CheckedType, second CheckedType) CheckedType {
	return CheckedType{Kind: CuratedShape, Scalar: NotScalar, Curated: kind, Object: 0,
		First: lean.NewBox(first), Second: lean.NewBox(second)}
}

type typeFrame struct {
	Shape          TypeShape
	Source         Package
	Position       string
	Next           uint
	Pending        bool
	First, Second  CheckedType
	Fields         lean.List[CheckedField]
	Count, Default int
	SelfBox        bool
}

type typeWork struct {
	ID     TypeID
	Source Package
	Pos    string
}

type typeStack struct {
	Frame typeFrame
	Rest  lean.Box[typeStack]
}

type TypeWalk struct {
	Program    Program
	Seen       lean.OrderedSet[ObjectID]
	Events     lean.Array[TypeEvent]
	Value      CheckedType
	Diagnostic Diagnostic
	Cycle      lean.Array[string]
	Exhausted  bool
	work       lean.Option[typeWork]
	stack      lean.Box[typeStack]
}

// StartType creates an independent traversal rooted at a Go type reference.
//
//golean:export
func StartType(program Program, seen lean.OrderedSet[ObjectID], source Package, pos string, id TypeID) TypeWalk {
	work := typeWork{ID: id, Source: source, Pos: pos}
	return TypeWalk{Program: program, Seen: seen, Events: lean.Array[TypeEvent]{}, Value: noCheckedType(),
		Diagnostic: validDiagnostic(), Cycle: lean.Array[string]{}, Exhausted: false,
		work: lean.Some(work), stack: lean.Box[typeStack]{}}
}

// Pending reports whether this type traversal can advance.
//
//golean:export
func (s TypeWalk) Pending() bool {
	return s.Diagnostic.Code == Valid && s.Cycle.Size() == 0 && !s.Exhausted &&
		(s.work.IsSome() || s.stack.IsSome())
}

func (s TypeWalk) atWork(work lean.Option[typeWork], stack lean.Box[typeStack], value CheckedType) TypeWalk {
	return TypeWalk{Program: s.Program, Seen: s.Seen, Events: s.Events, Value: value,
		Diagnostic: s.Diagnostic, Cycle: s.Cycle, Exhausted: s.Exhausted, work: work, stack: stack}
}

func (s TypeWalk) failed(diagnostic Diagnostic) TypeWalk {
	return TypeWalk{Program: s.Program, Seen: s.Seen, Events: s.Events, Value: s.Value,
		Diagnostic: diagnostic, Cycle: s.Cycle, Exhausted: s.Exhausted, work: s.work, stack: s.stack}
}

func (s TypeWalk) withEvent(event TypeEvent) TypeWalk {
	return TypeWalk{Program: s.Program, Seen: s.Seen, Events: s.Events.Push(event), Value: s.Value,
		Diagnostic: s.Diagnostic, Cycle: s.Cycle, Exhausted: s.Exhausted, work: s.work, stack: s.stack}
}

func (s TypeWalk) mark(id ObjectID) TypeWalk {
	return TypeWalk{Program: s.Program, Seen: s.Seen.Insert(id), Events: s.Events, Value: s.Value,
		Diagnostic: s.Diagnostic, Cycle: s.Cycle, Exhausted: s.Exhausted, work: s.work, stack: s.stack}
}

func (s TypeWalk) checkEnum(id ObjectID) TypeWalk {
	checked := s.Program.CheckEnumZero(id)
	return TypeWalk{Program: s.Program, Seen: s.Seen, Events: s.Events, Value: s.Value,
		Diagnostic: s.Diagnostic, Cycle: checked.Cycle, Exhausted: checked.Exhausted, work: s.work, stack: s.stack}
}

func typeRef(kind TypeShapeKind, id ObjectID) CheckedType {
	return CheckedType{Kind: kind, Scalar: NotScalar, Curated: UnknownCuratedType, Object: id,
		First: lean.Box[CheckedType]{}, Second: lean.Box[CheckedType]{}}
}

func beginTypeFrame(shape TypeShape, source Package, pos string) typeFrame {
	return typeFrame{Shape: shape, Source: source, Position: pos, Next: 0, Pending: false,
		First: noCheckedType(), Second: noCheckedType(), Fields: lean.List[CheckedField]{}, Count: 0, Default: 0, SelfBox: false}
}

func (s TypeWalk) pushTypeFrame(frame typeFrame) TypeWalk {
	stack := lean.NewBox(typeStack{Frame: frame, Rest: s.stack})
	return s.atWork(lean.None[typeWork](), stack, s.Value)
}

func (s TypeWalk) addDependency(source Package, obj Object, pos string) TypeWalk {
	if source.Path == obj.Package {
		return s
	}
	target := s.Program.PackageOrMissing(obj.Package)
	issue := source.ValidateDependency(target, obj.Package, pos)
	if issue.Code != Valid {
		return s.failed(issue)
	}
	return s.withEvent(TypeEvent{Package: source.Path, Dependency: obj.Package, Declaration: lean.None[CheckedTypeDeclaration]()})
}

func (s TypeWalk) enterType(work typeWork) TypeWalk {
	shape := s.Program.ClassifyType(work.ID, work.Source.WordBits, work.Pos)
	if shape.Diagnostic.Code != Valid {
		return s.failed(shape.Diagnostic)
	}
	if shape.Kind == ScalarShape {
		return s.atWork(lean.None[typeWork](), s.stack, checkedScalar(shape.Scalar))
	}
	if shape.Kind == CuratedShape {
		return s.pushTypeFrame(beginTypeFrame(shape, work.Source, work.Pos))
	}
	obj := s.Program.ObjectOrMissing(shape.Object)
	withDependency := s.addDependency(work.Source, obj, work.Pos)
	if withDependency.Diagnostic.Code != Valid {
		return withDependency
	}
	if s.Seen.Contains(shape.Object) {
		return withDependency.atWork(lean.None[typeWork](), s.stack, typeRef(shape.Kind, shape.Object))
	}
	return withDependency.enterNamed(shape, obj, work.Pos)
}

func (s TypeWalk) enterNamed(shape TypeShape, obj Object, pos string) TypeWalk {
	owner := s.Program.PackageOrMissing(obj.Package)
	frame := beginTypeFrame(shape, owner, pos)
	if shape.Kind == EnumShape {
		checked := s.checkEnum(shape.Object)
		if checked.Cycle.Size() != 0 || checked.Exhausted {
			return checked.failed(Diagnostic{Code: Valid, Pos: obj.Pos, Detail: ""})
		}
		return checked.mark(shape.Object).pushTypeFrame(frame)
	}
	return s.mark(shape.Object).pushTypeFrame(frame)
}

func (s TypeWalk) enqueueType(frame typeFrame, stack lean.Box[typeStack], id TypeID, pos string) TypeWalk {
	pending := typeFrame{Shape: frame.Shape, Source: frame.Source, Position: frame.Position, Next: frame.Next,
		Pending: true, First: frame.First, Second: frame.Second, Fields: frame.Fields, Count: frame.Count,
		Default: frame.Default, SelfBox: frame.SelfBox}
	work := typeWork{ID: id, Source: frame.Source, Pos: pos}
	return s.atWork(lean.Some(work), lean.NewBox(typeStack{Frame: pending, Rest: stack}), s.Value)
}

func (s TypeWalk) advanceCurated(frame typeFrame, stack lean.Box[typeStack]) TypeWalk {
	if frame.Pending {
		first := typeArgument(frame.First, s.Value, frame.Next == 0)
		second := typeArgument(frame.Second, s.Value, frame.Next == 1)
		next := typeFrame{Shape: frame.Shape, Source: frame.Source, Position: frame.Position, Next: frame.Next + 1,
			Pending: false, First: first, Second: second, Fields: frame.Fields, Count: 0, Default: 0, SelfBox: false}
		return s.atWork(lean.None[typeWork](), stack, s.Value).pushTypeFrame(next)
	}
	if frame.Next < frame.Shape.Arguments.Size() {
		return s.enqueueType(frame, stack, frame.Shape.Arguments.Get(frame.Next).UnwrapOr(0), frame.Position)
	}
	value := checkedCurated(frame.Shape.Curated, frame.First, frame.Second)
	return s.atWork(lean.None[typeWork](), stack, value)
}

func typeArgument(previous CheckedType, value CheckedType, replace bool) CheckedType {
	if replace {
		return value
	}
	return previous
}

func (s TypeWalk) advanceNamed(frame typeFrame, stack lean.Box[typeStack]) TypeWalk {
	obj := s.Program.ObjectOrMissing(frame.Shape.Object)
	if frame.Shape.Kind == EnumShape {
		spec := obj.Enum.UnwrapOr(Enum{Payloads: lean.Array[ObjectID]{}, Default: ""})
		return s.advanceFields(frame, stack, obj, spec.Payloads, spec.Default)
	}
	return s.advanceFields(frame, stack, obj, frame.Shape.Fields, "")
}

func (s TypeWalk) advanceFields(frame typeFrame, stack lean.Box[typeStack], obj Object, fields lean.Array[ObjectID], defaultName string) TypeWalk {
	if frame.Next >= fields.Size() {
		return s.finishNamed(frame, stack, obj)
	}
	field := s.Program.ObjectOrMissing(fields.Get(frame.Next).UnwrapOr(0))
	if frame.Pending {
		return s.recordField(frame, stack, field.Name, s.Value, defaultName, false)
	}
	if frame.Shape.Kind == RecordShape {
		issue := field.ValidateField()
		if issue.Code != Valid {
			return s.failed(issue)
		}
		if s.Program.IsSelfBox(field.Type, frame.Shape.Object) {
			boxed := checkedCurated(CuratedBox, typeRef(frame.Shape.Kind, frame.Shape.Object), noCheckedType())
			return s.recordField(frame, stack, field.Name, boxed, "", true)
		}
	}
	return s.enqueueType(frame, stack, field.Type, field.Pos)
}

func (s TypeWalk) recordField(frame typeFrame, stack lean.Box[typeStack], name string, value CheckedType, defaultName string, selfBox bool) TypeWalk {
	defaultIndex := chooseDefault(frame, name, defaultName)
	next := typeFrame{Shape: frame.Shape, Source: frame.Source, Position: frame.Position, Next: frame.Next + 1, Pending: false,
		First: frame.First, Second: frame.Second, Fields: lean.Cons(CheckedField{Name: name, Type: value}, frame.Fields),
		Count: frame.Count + 1, Default: defaultIndex, SelfBox: frame.SelfBox || selfBox}
	return s.atWork(lean.None[typeWork](), stack, s.Value).pushTypeFrame(next)
}

func chooseDefault(frame typeFrame, name string, defaultName string) int {
	if name == defaultName {
		return frame.Count
	}
	return frame.Default
}

func prependTypeField(field CheckedField, fields lean.List[CheckedField]) lean.List[CheckedField] {
	return lean.Cons(field, fields)
}

func (s TypeWalk) finishNamed(frame typeFrame, stack lean.Box[typeStack], obj Object) TypeWalk {
	fields := lean.FoldList(frame.Fields, lean.List[CheckedField]{}, prependTypeField)
	decl := CheckedTypeDeclaration{Kind: frame.Shape.Kind, Object: frame.Shape.Object, Fields: fields,
		Default: frame.Default, SelfBox: frame.SelfBox}
	result := s.atWork(lean.None[typeWork](), stack, typeRef(frame.Shape.Kind, frame.Shape.Object))
	return result.withEvent(TypeEvent{Package: obj.Package, Dependency: "", Declaration: lean.Some(decl)})
}

// AdvanceType runs one type-checking transition and records its declaration
// and dependency effects in encounter order.
//
//golean:export
func AdvanceType(s TypeWalk) TypeWalk {
	if !s.Pending() {
		return s
	}
	if s.work.IsSome() {
		work := s.work.UnwrapOr(typeWork{ID: 0, Source: s.Program.PackageOrMissing(""), Pos: ""})
		return s.enterType(work)
	}
	top := s.stack.Get()
	if top.Frame.Shape.Kind == CuratedShape {
		return s.advanceCurated(top.Frame, top.Rest)
	}
	return s.advanceNamed(top.Frame, top.Rest)
}
