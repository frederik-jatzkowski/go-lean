package lower

import (
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
)

var binaryOps = map[token.Token]ir.BinaryOp{
	token.ADD: ir.Add, token.SUB: ir.Sub, token.EQL: ir.Eq, token.NEQ: ir.Ne,
	token.LSS: ir.Lt, token.LEQ: ir.Le, token.GTR: ir.Gt, token.GEQ: ir.Ge,
	token.LAND: ir.And, token.LOR: ir.Or,
}

func (f *function) expr(node ast.Expr) (ir.Expr, error) {
	p := f.source.Package
	info := p.TypesInfo
	if paren, ok := node.(*ast.ParenExpr); ok {
		return f.expr(paren.X)
	}
	if binary, ok := node.(*ast.BinaryExpr); ok && binaryOps[binary.Op] == 0 {
		return nil, load.Error(p, node.Pos(), "unsupported binary operator %s", binary.Op)
	}
	tv := info.Types[node]
	if tv.Value != nil {
		if err := f.constantOperands(node); err != nil {
			return nil, err
		}
		t, err := f.goType(p, node.Pos(), tv.Type)
		if err != nil {
			return nil, err
		}
		value := tv.Value.ExactString()
		if t.Kind == ir.String {
			value = constant.StringVal(tv.Value)
		}
		return ir.Constant{Type: t, Value: value}, nil
	}
	switch e := node.(type) {
	case *ast.Ident:
		v, ok := info.Uses[e].(*types.Var)
		id, found := f.locals[v]
		if !ok || !found {
			return nil, load.Error(p, e.Pos(), "expected an immutable local or constant, got %s", e.Name)
		}
		return ir.Local{ID: id}, nil
	case *ast.UnaryExpr:
		if e.Op == token.NOT {
			value, err := f.expr(e.X)
			return ir.Unary{Op: ir.Not, Value: value}, err
		}
	case *ast.BinaryExpr:
		t, err := f.goType(p, e.X.Pos(), info.TypeOf(e.X))
		if err != nil {
			return nil, err
		}
		op := binaryOps[e.Op]
		if t.Kind >= ir.Record || ((op == ir.Add || op == ir.Sub) && t.Kind < ir.Int8) {
			return nil, load.Error(p, e.Pos(), "unsupported operands for %s", e.Op)
		}
		left, err := f.expr(e.X)
		if err != nil {
			return nil, err
		}
		right, err := f.expr(e.Y)
		return ir.Binary{Op: op, Kind: t.Kind, Left: left, Right: right}, err
	case *ast.SelectorExpr:
		sel := info.Selections[e]
		if sel != nil && sel.Kind() == types.FieldVal && !sel.Indirect() && len(sel.Index()) == 1 {
			if _, err := f.goType(p, e.X.Pos(), sel.Recv()); err != nil {
				return nil, err
			}
			receiver, err := f.expr(e.X)
			return ir.FieldRead{Record: receiver, Name: sel.Obj().Name()}, err
		}
	case *ast.CompositeLit:
		return f.literal(e)
	case *ast.CallExpr:
		return f.call(e)
	}
	return nil, load.Error(p, node.Pos(), "unsupported expression %T", node)
}

// Go's type checker evaluates constants. Validate inline operands as well so
// constant folding cannot hide Go syntax outside the supported subset.
func (f *function) constantOperands(node ast.Expr) error {
	p := f.source.Package
	var operands []ast.Expr
	switch e := node.(type) {
	case *ast.BinaryExpr:
		operands = []ast.Expr{e.X, e.Y}
	case *ast.UnaryExpr:
		if e.Op != token.SUB && e.Op != token.ADD && e.Op != token.NOT {
			return load.Error(p, e.Pos(), "unsupported unary operator %s", e.Op)
		}
		operands = []ast.Expr{e.X}
	case *ast.CallExpr:
		if !p.TypesInfo.Types[e.Fun].IsType() {
			return load.Error(p, e.Pos(), "unsupported constant builtin call")
		}
		operands = e.Args
	}
	for _, operand := range operands {
		if _, err := f.expr(operand); err != nil {
			return err
		}
	}
	return nil
}

func (f *function) literal(e *ast.CompositeLit) (ir.Expr, error) {
	p := f.source.Package
	typ := p.TypesInfo.TypeOf(e)
	t, err := f.goType(p, e.Pos(), typ)
	if err != nil {
		return nil, err
	}
	if t.Kind > ir.Record && len(e.Elts) == 0 {
		return ir.Primitive{Op: ir.Empty, Type: t}, nil
	}
	if t.Kind != ir.Record {
		return nil, load.Error(p, e.Pos(), "expected a record literal or an empty curated value")
	}
	record := typ.Underlying().(*types.Struct)
	if len(e.Elts) != record.NumFields() {
		return nil, load.Error(p, e.Pos(), "record literals must initialize every field")
	}
	fields := make([]ir.Expr, record.NumFields())
	for _, el := range e.Elts {
		kv, ok := el.(*ast.KeyValueExpr)
		if !ok {
			return nil, load.Error(p, el.Pos(), "record literals require keyed fields")
		}
		name := kv.Key.(*ast.Ident).Name
		for i := 0; i < record.NumFields(); i++ {
			if record.Field(i).Name() != name {
				continue
			}
			fields[i], err = f.expr(kv.Value)
			if err != nil {
				return nil, err
			}
			break
		}
	}
	return ir.StructLiteral{Type: t.Record, Fields: fields}, nil
}

var constructors = map[string]ir.PrimitiveOp{
	"Some": ir.Some, "None": ir.None, "Nil": ir.Nil, "Cons": ir.Cons, "NewBitVec": ir.NewBitVec,
}

var methods = map[ir.Kind]map[string]ir.PrimitiveOp{
	ir.Array:     {"Push": ir.Push, "Pop": ir.Pop, "Get": ir.Get, "Set": ir.Set, "Size": ir.Size},
	ir.ByteArray: {"Push": ir.Push, "Get": ir.Get, "Set": ir.Set, "Size": ir.Size, "Extract": ir.Extract},
	ir.RBMap:     {"Find": ir.Find, "Contains": ir.Contains, "Insert": ir.Insert, "Erase": ir.Erase},
	ir.RBSet:     {"Contains": ir.Contains, "Insert": ir.Insert, "Erase": ir.Erase},
	ir.Option:    {"IsSome": ir.IsSome, "UnwrapOr": ir.UnwrapOr},
	ir.List:      {"IsEmpty": ir.IsEmpty},
	ir.BitVec:    {"Get": ir.Get, "Set": ir.Set, "Width": ir.Width, "ToUint64": ir.ToUint64},
}

func callBase(e ast.Expr) ast.Expr {
	for {
		switch node := e.(type) {
		case *ast.ParenExpr:
			e = node.X
		case *ast.IndexExpr:
			e = node.X
		case *ast.IndexListExpr:
			e = node.X
		default:
			return e
		}
	}
}

func (f *function) call(e *ast.CallExpr) (ir.Expr, error) {
	p := f.source.Package
	info := p.TypesInfo
	var fn *types.Func
	var receiver ast.Expr
	var selection *types.Selection
	switch target := callBase(e.Fun).(type) {
	case *ast.Ident:
		fn, _ = info.Uses[target].(*types.Func)
	case *ast.SelectorExpr:
		fn, _ = info.Uses[target.Sel].(*types.Func)
		selection = info.Selections[target]
		if selection != nil && selection.Kind() == types.MethodVal {
			receiver = target.X
		}
	}
	if fn == nil || fn.Pkg() == nil || e.Ellipsis.IsValid() {
		return nil, load.Error(p, e.Pos(), "expected a direct call to a supported function")
	}
	if fn.Pkg().Path() == load.Curated {
		var t ir.Type
		var op ir.PrimitiveOp
		var err error
		nodes := e.Args
		if selection == nil {
			op = constructors[fn.Name()]
			if op != 0 {
				t, err = f.goType(p, e.Pos(), info.TypeOf(e))
			}
		} else if receiver != nil && !selection.Indirect() && len(selection.Index()) == 1 {
			t, err = f.goType(p, receiver.Pos(), selection.Recv())
			op = methods[t.Kind][fn.Name()]
			nodes = append([]ast.Expr{receiver}, e.Args...)
		}
		if err != nil {
			return nil, err
		}
		if op == 0 {
			return nil, load.Error(p, e.Pos(), "unsupported curated operation %s", fn.Name())
		}
		args, err := f.arguments(nodes)
		return ir.Primitive{Op: op, Type: t, Args: args}, err
	}
	if selection != nil || fn.Signature().Recv() != nil {
		return nil, load.Error(p, e.Pos(), "only curated value methods are supported")
	}
	args, err := f.arguments(e.Args)
	if err != nil {
		return nil, err
	}
	if _, ok := f.contracts[fn]; ok {
		f.contracts[fn] = true
		return ir.AbstractCall{Target: symbol(fn), Args: args}, nil
	}
	if fn.Pkg().Path() != p.PkgPath {
		if !f.compiler.source.Functions[fn].Export {
			return nil, load.Error(p, e.Pos(), "cross-package call to %s requires golean:export or a contract", fn.FullName())
		}
		if err := f.depend(p, fn.Pkg().Path(), e.Pos()); err != nil {
			return nil, err
		}
	}
	if f.state[fn] == 1 {
		return nil, load.Error(p, e.Pos(), "recursive call to %s", fn.FullName())
	}
	if err := f.function(fn); err != nil {
		return nil, err
	}
	if f.abstract[fn] {
		return nil, load.Error(p, e.Pos(), "cannot call a function with caller-local contracts")
	}
	return ir.Call{Target: symbol(fn), Args: args}, nil
}

func (f *function) arguments(nodes []ast.Expr) ([]ir.Expr, error) {
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
