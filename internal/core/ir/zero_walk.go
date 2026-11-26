package ir

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type zeroStep uint8

const (
	visitZero zeroStep = iota + 1
	wrapZeroEnum
	wrapZeroRecord
	wrapZeroFold
	cacheZeroNamed
)

type zeroFrame struct {
	Step    zeroStep
	Type    Type
	Symbol  Symbol
	Variant string
	Fields  lean.Array[Field]
	Results lean.Array[Expr]
	Index   uint
}

type zeroStack struct {
	Frame zeroFrame
	Rest  lean.Box[zeroStack]
}

type ZeroWalk struct {
	Value Expr
	stack lean.Box[zeroStack]
	Memo  lean.OrderedMap[string, lean.OrderedMap[string, Expr]]
}

type ZeroTransition struct {
	Walk             ZeroWalk
	NeedsDeclaration bool
	Symbol           Symbol
}

func zeroVisit(t Type) zeroFrame {
	return zeroFrame{Step: visitZero, Type: t, Symbol: Symbol{Package: "", Name: ""}, Variant: "",
		Fields: lean.Array[Field]{}, Results: lean.Array[Expr]{}, Index: 0}
}

// StartZero constructs the zero value of a resolved IR type.
//
//golean:export
func StartZero(t Type) ZeroWalk {
	return ZeroWalk{Value: Expr{}, Memo: lean.OrderedMap[string, lean.OrderedMap[string, Expr]]{}, stack: lean.NewBox(zeroStack{Frame: zeroVisit(t), Rest: lean.Box[zeroStack]{}})}
}

// Pending reports whether zero-value construction has work remaining.
//
//golean:export
func (w ZeroWalk) Pending() bool {
	return w.stack.IsSome()
}

func (w ZeroWalk) push(frame zeroFrame) ZeroWalk {
	return ZeroWalk{Value: w.Value, Memo: w.Memo, stack: lean.NewBox(zeroStack{Frame: frame, Rest: w.stack})}
}

func (w ZeroWalk) withValue(value Expr) ZeroWalk {
	return ZeroWalk{Value: value, Memo: w.Memo, stack: w.stack}
}

func (w ZeroWalk) next() ZeroTransition {
	return ZeroTransition{Walk: w, NeedsDeclaration: false, Symbol: Symbol{Package: "", Name: ""}}
}

func (w ZeroWalk) request(symbol Symbol) ZeroTransition {
	return ZeroTransition{Walk: w, NeedsDeclaration: true, Symbol: symbol}
}

// AdvanceZero executes one transition and requests a named declaration when
// its fields are needed.
//
//golean:export
func AdvanceZero(w ZeroWalk) ZeroTransition {
	if !w.Pending() {
		return w.next()
	}
	frame := w.stack.Get()
	rest := ZeroWalk{Value: w.Value, Memo: w.Memo, stack: frame.Rest}
	if frame.Frame.Step == visitZero {
		return rest.visitZeroType(frame.Frame.Type)
	}
	if frame.Frame.Step == wrapZeroEnum {
		return rest.withValue(NewExprConstructor(Constructor{Enum: frame.Frame.Symbol, Variant: frame.Frame.Variant, Value: w.Value})).next()
	}
	if frame.Frame.Step == wrapZeroRecord {
		return rest.collectZeroField(frame.Frame).next()
	}
	if frame.Frame.Step == wrapZeroFold {
		stop := NewExprConstant(Constant{Type: NewTypeScalarType(ScalarType{Scalar: Bool}), Value: "false"})
		return rest.withValue(NewExprFoldControlLiteral(FoldControlLiteral{State: w.Value, Stop: stop})).next()
	}
	if frame.Frame.Step == cacheZeroNamed {
		return rest.saveZero(frame.Frame.Symbol).next()
	}
	return rest.next()
}

func (w ZeroWalk) visitZeroType(t Type) ZeroTransition {
	switch form := t.Case().(type) {
	case EnumTypeRef:
		return w.request(form.Symbol)
	case RecordType:
		return w.request(form.Symbol)
	case FoldControlType:
		frame := zeroFrame{Step: wrapZeroFold, Type: Type{}, Symbol: Symbol{Package: "", Name: ""},
			Variant: "", Fields: lean.Array[Field]{}, Results: lean.Array[Expr]{}, Index: 0}
		return w.push(frame).push(zeroVisit(form.Element)).next()
	case ScalarType:
		return w.withValue(NewExprConstant(Constant{Type: t, Value: scalarZero(form.Scalar)})).next()
	case MissingType:
		return w.withValue(NewExprConstant(Constant{Type: t, Value: "0"})).next()
	case ArrayType:
		return w.withValue(NewEmptyValueExpr(t)).next()
	case ByteArrayType:
		return w.withValue(NewEmptyValueExpr(t)).next()
	case MapType:
		return w.withValue(NewEmptyValueExpr(t)).next()
	case SetType:
		return w.withValue(NewEmptyValueExpr(t)).next()
	case OptionType:
		return w.withValue(NewEmptyValueExpr(t)).next()
	case BitVecType:
		return w.withValue(NewEmptyValueExpr(t)).next()
	case ListType:
		return w.withValue(NewEmptyValueExpr(t)).next()
	case BoxType:
		return w.withValue(NewEmptyValueExpr(t)).next()
	}
	return w.next()
}

func scalarZero(kind Kind) string {
	if kind == Bool {
		return "false"
	}
	if kind == String {
		return ""
	}
	return "0"
}

// WithZeroDeclaration continues after the compiler resolves a named type.
//
//golean:export
func (w ZeroWalk) WithZeroDeclaration(decl Declaration) ZeroWalk {
	switch item := decl.Case().(type) {
	case Enum:
		return w.zeroEnum(item)
	case Struct:
		return w.zeroRecord(item)
	case MissingDeclaration:
		return w
	case Mutual:
		return w
	case TypeAlias:
		return w
	case NamedConstant:
		return w
	case Function:
		return w
	case Contract:
		return w
	}
	return w
}

type zeroVariant struct {
	Index int
	Field Field
}

func selectZeroVariant(field Field, state zeroVariant) lean.FoldControl[zeroVariant] {
	if state.Index == 0 {
		return lean.FoldControl[zeroVariant]{State: zeroVariant{Index: 0, Field: field}, Stop: true}
	}
	next := zeroVariant{Index: state.Index - 1, Field: state.Field}
	return lean.FoldControl[zeroVariant]{State: next, Stop: false}
}

func (w ZeroWalk) zeroEnum(enum Enum) ZeroWalk {
	initial := zeroVariant{Index: enum.Default, Field: Field{Name: "", Type: Type{}}}
	field := lean.FoldListUntil(enum.Variants, initial, selectZeroVariant).State.Field
	wrapper := zeroFrame{Step: wrapZeroEnum, Type: Type{}, Symbol: enum.Symbol, Variant: field.Name,
		Fields: lean.Array[Field]{}, Results: lean.Array[Expr]{}, Index: 0}
	return w.push(wrapper).push(zeroVisit(field.Type))
}

func (w ZeroWalk) zeroRecord(record Struct) ZeroWalk {
	fields := lean.FoldList(record.Fields, lean.Array[Field]{}, appendZeroField)
	frame := zeroFrame{Step: wrapZeroRecord, Type: Type{}, Symbol: record.Symbol, Variant: "",
		Fields: fields, Results: lean.Array[Expr]{}, Index: 0}
	return w.visitZeroField(frame)
}

func appendZeroField(field Field, fields lean.Array[Field]) lean.Array[Field] {
	return fields.Push(field)
}

func (w ZeroWalk) collectZeroField(frame zeroFrame) ZeroWalk {
	next := zeroFrame{Step: wrapZeroRecord, Type: Type{}, Symbol: frame.Symbol, Variant: "",
		Fields: frame.Fields, Results: frame.Results.Push(w.Value), Index: frame.Index + 1}
	return w.visitZeroField(next)
}

type zeroSequence struct {
	Values lean.Array[Expr]
	Result ExprSeq
}

func prependZeroValue(index uint, state zeroSequence) zeroSequence {
	value := state.Values.Get(state.Values.Size() - 1 - index).UnwrapOr(Expr{})
	next := ExprSeq{First: lean.NewBox(ExprSeqItem{Value: value, Rest: state.Result})}
	return zeroSequence{Values: state.Values, Result: next}
}

func (w ZeroWalk) visitZeroField(frame zeroFrame) ZeroWalk {
	if frame.Index >= frame.Fields.Size() {
		initial := zeroSequence{Values: frame.Results, Result: ExprSeq{First: lean.Box[ExprSeqItem]{}}}
		sequence := lean.FoldN(frame.Results.Size(), initial, prependZeroValue).Result
		return w.withValue(NewExprStructLiteral(StructLiteral{Type: frame.Symbol, Fields: sequence}))
	}
	field := frame.Fields.Get(frame.Index).UnwrapOr(Field{Name: "", Type: Type{}})
	return w.push(frame).push(zeroVisit(field.Type))
}

func (w ZeroWalk) saveZero(id Symbol) ZeroWalk {
	pkg := w.Memo.Find(id.Package).UnwrapOr(lean.OrderedMap[string, Expr]{})
	return ZeroWalk{Value: w.Value, stack: w.stack, Memo: w.Memo.Insert(id.Package, pkg.Insert(id.Name, w.Value))}
}

func (w ZeroWalk) WithNamedZero(id Symbol, declared Declaration) ZeroWalk {
	pkg := w.Memo.Find(id.Package).UnwrapOr(lean.OrderedMap[string, Expr]{})
	cached := pkg.Find(id.Name)
	if cached.IsSome() {
		return w.withValue(cached.UnwrapOr(Expr{}))
	}
	frame := zeroFrame{Step: cacheZeroNamed, Type: Type{}, Symbol: id, Variant: "",
		Fields: lean.Array[Field]{}, Results: lean.Array[Expr]{}, Index: 0}
	return w.push(frame).WithZeroDeclaration(declared)
}
