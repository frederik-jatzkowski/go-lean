package lower

import (
	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
)

var binaryOps = map[string]ir.BinaryOp{
	"+": ir.Add, "-": ir.Sub, "==": ir.Eq, "!=": ir.Ne,
	"<": ir.Lt, "<=": ir.Le, ">": ir.Gt, ">=": ir.Ge,
	"&&": ir.And, "||": ir.Or,
}

func (f *function) inputExpr(id loaded.ExprID) loaded.Expression {
	return f.compiler.source.LookupExpression(id).UnwrapOr(loaded.Expression{})
}

func (f *function) expr(id loaded.ExprID) (ir.Expr, error) {
	p := f.pkg
	e := f.inputExpr(id)
	if form, ok := e.Form.Case().(loaded.Parenthesized); ok {
		return f.expr(form.Inner)
	}
	if err := subsetError(e.Validate()); err != nil {
		return ir.Expr{}, err
	}
	if e.Constant.Present {
		if err := f.constantOperands(e); err != nil {
			return ir.Expr{}, err
		}
		t, err := f.goType(p, e.Pos, e.Type)
		if err != nil {
			return ir.Expr{}, err
		}
		return ir.NewExprConstant(ir.Constant{Type: t, Value: e.Constant.Value}), nil
	}
	switch form := e.Form.Case().(type) {
	case loaded.Identifier:
		id, found := f.locals[form.Object]
		if !found {
			return ir.Expr{}, diagnostic(e.Pos, "expected an immutable local or constant, got %s", form.Name)
		}
		return ir.NewExprLocal(ir.Local{ID: id}), nil
	case loaded.UnaryExpr:
		value, err := f.expr(form.Operand)
		return ir.NewExprUnary(ir.Unary{Op: ir.Not, Value: value}), err
	case loaded.BinaryExpr:
		t, err := f.goType(p, f.inputExpr(form.Left).Pos, f.inputExpr(form.Left).Type)
		if err != nil {
			return ir.Expr{}, err
		}
		op := binaryOps[form.Operator]
		if t.Kind() >= ir.Record || ((op == ir.Add || op == ir.Sub) && t.Kind() < ir.Int8) {
			return ir.Expr{}, diagnostic(e.Pos, "unsupported operands for %s", form.Operator)
		}
		left, err := f.expr(form.Left)
		if err != nil {
			return ir.Expr{}, err
		}
		right, err := f.expr(form.Right)
		return ir.NewExprBinary(ir.Binary{Op: op, Kind: t.Kind(), Left: left, Right: right}), err
	case loaded.SelectorExpr:
		sel := form.Selection
		t, err := f.goType(p, f.inputExpr(form.Base).Pos, sel.Receiver)
		if err != nil {
			return ir.Expr{}, err
		}
		if t.Kind() == ir.EnumType {
			return ir.Expr{}, diagnostic(e.Pos, "generated enum storage is private to lean.gen.go")
		}
		receiver, err := f.expr(form.Base)
		name := f.object(sel.Object).Name
		if t.Kind() == ir.FoldControl {
			if name == "Stop" {
				return ir.NewExprFoldStopRead(ir.FoldStopRead{Control: receiver}), err
			}
			return ir.NewExprFoldStateRead(ir.FoldStateRead{Control: receiver}), err
		}
		return ir.NewExprFieldRead(ir.FieldRead{Record: receiver, Name: name}), err
	case loaded.CompositeExpr:
		return f.literal(e, form)
	case loaded.CallExpr:
		if form.Conversion {
			return f.scalarConversion(e, form)
		}
		return f.call(e, form)
	}
	panic("invalid expression passed validation")
}

func (f *function) scalarConversion(e loaded.Expression, call loaded.CallExpr) (ir.Expr, error) {
	if call.Args.Size() == 1 {
		id := at(call.Args, uint(0))
		operand := f.inputExpr(id)
		if f.underlying(e.Type).AllowsIdentityConversion(f.underlying(operand.Type)) {
			if _, err := f.goType(f.pkg, e.Pos, e.Type); err != nil {
				return ir.Expr{}, err
			}
			if _, err := f.goType(f.pkg, operand.Pos, operand.Type); err != nil {
				return ir.Expr{}, err
			}
			return f.expr(id)
		}
	}
	return ir.Expr{}, diagnostic(e.Pos, "expected a direct call to a supported function")
}

// Go's type checker evaluates constants. Validate inline operands as well so
// constant folding cannot hide Go syntax outside the supported subset.
func (f *function) constantOperands(e loaded.Expression) error {
	var operands []loaded.ExprID
	switch form := e.Form.Case().(type) {
	case loaded.BinaryExpr:
		operands = []loaded.ExprID{form.Left, form.Right}
	case loaded.UnaryExpr:
		operands = []loaded.ExprID{form.Operand}
	case loaded.CallExpr:
		operands = values(form.Args)
	}
	for _, operand := range operands {
		if _, err := f.expr(operand); err != nil {
			return err
		}
	}
	return nil
}

func (f *function) literal(e loaded.Expression, form loaded.CompositeExpr) (ir.Expr, error) {
	p := f.pkg
	typ := e.Type
	t, err := f.goType(p, e.Pos, typ)
	if err != nil {
		return ir.Expr{}, err
	}
	if t.Kind() == ir.EnumType {
		if form.Elements.Size() != 0 {
			return ir.Expr{}, diagnostic(e.Pos, "construct enum values with generated constructors or an empty literal")
		}
		return f.zero(t), nil
	}
	if t.Kind() > ir.Record && t.Kind() != ir.FoldControl && form.Elements.Size() == 0 {
		return ir.NewEmptyValueExpr(t), nil
	}
	if t.Kind() != ir.Record && t.Kind() != ir.FoldControl {
		return ir.Expr{}, diagnostic(e.Pos, "expected a record literal or an empty curated value")
	}
	record := values(f.underlying(typ).Fields)
	if int(form.Elements.Size()) != len(record) {
		return ir.Expr{}, diagnostic(e.Pos, "record literals must initialize every field")
	}
	fields := make([]ir.Expr, len(record))
	for _, el := range values(form.Elements) {
		element := f.inputExpr(el)
		kv, ok := element.Form.Case().(loaded.KeyedExpr)
		if !ok {
			return ir.Expr{}, diagnostic(element.Pos, "record literals require keyed fields")
		}
		for i, field := range record {
			if f.object(field).Name != kv.Name {
				continue
			}
			fields[i], err = f.expr(kv.Value)
			if err != nil {
				return ir.Expr{}, err
			}
			break
		}
	}

	if t.Kind() == ir.FoldControl {
		return ir.NewExprFoldControlLiteral(ir.FoldControlLiteral{State: fields[0], Stop: fields[1]}), nil
	}
	return ir.NewExprStructLiteral(ir.StructLiteral{Type: t.Case().(ir.RecordType).Symbol, Fields: exprSeq(fields)}), nil
}

func (f *function) call(e loaded.Expression, form loaded.CallExpr) (ir.Expr, error) {
	p := f.pkg
	fn := form.Object
	obj := f.object(fn)
	receiver, selection := form.Receiver, form.Selection
	argsIn := values(form.Args)

	if err := subsetError(form.ValidateTarget(obj, e.Pos)); err != nil {
		return ir.Expr{}, err
	}
	if obj.Constructor.IsSome() {
		constructor := obj.Constructor.UnwrapOr(loaded.EnumConstructor{})
		typ, err := f.goType(p, e.Pos, f.object(constructor.Owner).Type)
		if err != nil {
			return ir.Expr{}, err
		}
		value, err := f.expr(argsIn[0])
		return ir.NewExprConstructor(ir.Constructor{Enum: typ.Case().(ir.EnumTypeRef).Symbol, Variant: constructor.Variant, Value: value}), err
	}
	if obj.Package == loaded.Curated {
		if kind := folds[obj.Name]; selection.Kind == loaded.NoSelection && kind != 0 {
			return f.fold(e, form, kind)
		}
		var t ir.Type
		var op loaded.PrimitiveOp
		var err error
		nodes := argsIn
		if selection.Kind == loaded.NoSelection {
			op = loaded.CuratedConstructor(obj.Name)
			if op != 0 {
				t, err = f.goType(p, e.Pos, e.Type)
			}
		} else if receiver != 0 && selection.Direct {
			t, err = f.goType(p, f.inputExpr(receiver).Pos, selection.Receiver)
			op = loaded.CuratedMethod(f.object(f.unalias(selection.Receiver).Object).Name, obj.Name)
			nodes = append([]loaded.ExprID{receiver}, argsIn...)
		}
		if err != nil {
			return ir.Expr{}, err
		}
		if op == 0 {
			return ir.Expr{}, diagnostic(e.Pos, "unsupported curated operation %s", obj.Name)
		}
		args, err := f.arguments(nodes)
		if err != nil {
			return ir.Expr{}, err
		}
		return f.primitive(op, t, args), nil
	}
	nodes := argsIn
	if err := subsetError(form.ValidateReceiver(f.inputType(obj.Type), e.Pos)); err != nil {
		return ir.Expr{}, err
	}
	if receiver != 0 {
		nodes = append([]loaded.ExprID{receiver}, nodes...)
	}
	args, err := f.arguments(nodes)
	if err != nil {
		return ir.Expr{}, err
	}
	if fn == f.fn && f.source.Termination != "" {
		f.recursive = true
		return ir.NewExprCall(ir.Call{Target: f.symbol(fn), Args: exprSeq(args)}), nil
	}
	abstract, err := f.callTarget(fn, e.Pos)
	if err != nil {
		return ir.Expr{}, err
	}
	if abstract {
		return ir.NewExprAbstractCall(ir.AbstractCall{Target: f.symbol(fn), Args: exprSeq(args)}), nil
	}
	return ir.NewExprCall(ir.Call{Target: f.symbol(fn), Args: exprSeq(args)}), nil
}

func (f *function) callTarget(fn loaded.ObjectID, pos string) (bool, error) {
	p := f.pkg
	obj := f.object(fn)
	if _, ok := f.contracts[fn]; ok {
		f.contracts[fn] = true
		return true, nil
	}
	if obj.Package != p.Path {
		if !obj.Function.UnwrapOr(loaded.Function{}).Export {
			return false, diagnostic(pos, "cross-package call to %s requires golean:export or a contract", obj.FullName)
		}
		if err := f.depend(p, obj.Package, pos); err != nil {
			return false, err
		}
	}
	if f.state[fn] == 1 {
		return false, diagnostic(pos, "recursive call to %s", obj.FullName)
	}
	if err := f.function(fn); err != nil {
		return false, err
	}
	if f.abstract[fn] {
		return false, diagnostic(pos, "cannot call a function with caller-local contracts")
	}
	return false, nil
}

func (f *function) arguments(nodes []loaded.ExprID) ([]ir.Expr, error) {
	args := make([]ir.Expr, len(nodes))
	for i, node := range nodes {
		value, err := f.expr(node)
		if err != nil {
			return nil, err
		}
		args[i] = value
	}
	return args, nil
}
