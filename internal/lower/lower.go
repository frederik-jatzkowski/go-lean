// Package lower validates the supported Go subset and builds typed IR.
package lower

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"slices"
	"strconv"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
	"golang.org/x/tools/go/packages"
)

type compiler struct {
	source   *load.Program
	packages map[string]*packageBuilder
	state    map[types.Object]uint8
	abstract map[*types.Func]bool
	pending  []string
}

func Program(source *load.Program) ([]*ir.Package, error) {
	c := compiler{
		source:   source,
		packages: make(map[string]*packageBuilder),
		state:    make(map[types.Object]uint8),
		abstract: make(map[*types.Func]bool),
	}
	for _, path := range source.SelectedPackages {
		c.output(path)
	}
	for i := 0; i < len(c.pending); i++ {
		path := c.pending[i]
		p := source.Packages[path]
		for _, decl := range source.Declarations[path] {
			if err := c.declaration(p, decl); err != nil {
				return nil, err
			}
		}
	}
	builders := make([]*packageBuilder, 0, len(c.packages))
	for _, p := range c.packages {
		slices.Sort(p.imports)
		builders = append(builders, p)
	}
	slices.SortFunc(builders, func(a, b *packageBuilder) int { return strings.Compare(a.Path, b.Path) })
	result := make([]*ir.Package, 0, len(builders))
	for _, p := range builders {
		if issue := source.PackageIssues[p.Path]; issue != nil {
			return nil, issue
		}
		if err := groupTypes(p); err != nil {
			return nil, err
		}
		p.Imports = list(p.imports)
		p.LeanImports = list(p.leanImports)
		p.Decls = list(p.decls)
		p.Laws = list(p.laws)
		result = append(result, &p.Package)
	}
	return result, nil
}

func (c *compiler) declaration(p *packages.Package, decl load.Declaration) error {
	pos := decl.Pos
	switch obj := decl.Object.(type) {
	case *types.Func:
		if (obj.Name() == "init" && obj.Signature().Recv() == nil) || obj.Name() == "_" {
			return load.Error(p, pos, "unsupported function declaration %s", obj.Name())
		}
		return c.function(obj)
	case *types.TypeName:
		if alias, ok := obj.Type().(*types.Alias); ok && alias.TypeParams().Len() != 0 {
			return load.Error(p, pos, "unsupported generic type alias %s", obj.Name())
		}
		t, err := c.goType(p, pos, obj.Type())
		if err != nil {
			return err
		}
		if obj.Name() != "_" && ((t.Kind() != ir.Record && t.Kind() != ir.EnumType) || obj.IsAlias()) {
			out := c.output(p.PkgPath)
			out.decls = append(out.decls, ir.NewDeclarationTypeAlias(ir.TypeAlias{Symbol: symbol(obj), Type: t}))
		}
	case *types.Const:
		typ := types.Default(obj.Type())
		t, err := c.goType(p, pos, typ)
		if err != nil {
			return err
		}
		value := obj.Val().ExactString()
		switch obj.Val().Kind() {
		case constant.String:
			value = constant.StringVal(obj.Val())
		case constant.Int:
			if !fitsInteger(p.TypesSizes, typ, value) {
				return load.Error(p, pos, "constant %s is not representable as %s", obj.Name(), typ)
			}
		}
		if obj.Name() != "_" {
			out := c.output(p.PkgPath)
			out.decls = append(out.decls, ir.NewDeclarationNamedConstant(ir.NamedConstant{Symbol: symbol(obj), Value: ir.Constant{Type: t, Value: value}}))
		}
	case *types.Var:
		return load.Error(p, pos, "package variables are unsupported in modeled Go")
	default:
		return load.Error(p, pos, "unsupported package declaration")
	}
	return nil
}

func fitsInteger(sizes types.Sizes, typ types.Type, value string) bool {
	bits := int(sizes.Sizeof(typ)) * 8
	if typ.Underlying().(*types.Basic).Info()&types.IsUnsigned != 0 {
		_, err := strconv.ParseUint(value, 10, bits)
		return err == nil
	}
	_, err := strconv.ParseInt(value, 10, bits)
	return err == nil
}

func symbol(obj types.Object) ir.Symbol {
	name := obj.Name()
	if fn, ok := obj.(*types.Func); ok && fn.Signature().Recv() != nil {
		receiver := types.Unalias(fn.Signature().Recv().Type()).(*types.Named)
		name = receiver.Obj().Name() + "$" + name
	}
	return ir.Symbol{Package: obj.Pkg().Path(), Name: name}
}

func valueReceiver(fn *types.Func) bool {
	receiver := fn.Signature().Recv()
	if receiver == nil {
		return false
	}
	named, ok := types.Unalias(receiver.Type()).(*types.Named)
	return ok && !types.IsInterface(named)
}

type packageBuilder struct {
	ir.Package
	imports, leanImports []string
	decls                []ir.Declaration
	laws                 []ir.Law
}

func list[T any](values []T) lean.List[T] {
	var result lean.List[T]
	for i := len(values) - 1; i >= 0; i-- {
		result = lean.Cons(values[i], result)
	}
	return result
}

func exprSeq(values []ir.Expr) ir.ExprSeq {
	var result ir.ExprSeq
	for i := len(values) - 1; i >= 0; i-- {
		result = ir.ExprSeq{First: lean.NewBox(ir.ExprSeqItem{Value: values[i], Rest: result})}
	}
	return result
}

func isMissing(e ir.Expr) bool {
	_, missing := e.Case().(ir.MissingExpr)
	return missing
}

func (c *compiler) output(path string) *packageBuilder {
	if p := c.packages[path]; p != nil {
		return p
	}
	source := c.source.Packages[path]
	p := &packageBuilder{Package: ir.Package{Path: path, Name: source.Name, Dir: load.Dir(source)}}
	p.leanImports = slices.Clone(c.source.LeanImports[path])
	slices.Sort(p.leanImports)
	p.leanImports = slices.Compact(p.leanImports)
	if laws := c.source.PackageLaws[path]; len(laws) != 0 {
		for _, law := range laws {
			p.laws = append(p.laws, ir.Law{Proposition: law})
		}
	}
	p.Word = ir.UInt64
	if source.TypesSizes.Sizeof(types.Typ[types.Uint]) == 4 {
		p.Word = ir.UInt32
	}
	c.packages[path] = p
	if _, modeled := c.source.Declarations[path]; modeled {
		c.pending = append(c.pending, path)
	}
	return p
}

func (c *compiler) depend(p *packages.Package, path string, pos token.Pos) error {
	if p.PkgPath == path {
		return nil
	}
	if issue := c.source.PackageIssues[path]; issue != nil {
		return issue
	}
	target := c.source.Packages[path]
	if p.Module == nil || target == nil || target.Module == nil || target.Module.Path != p.Module.Path {
		return load.Error(p, pos, "concrete dependency %s must be in the same Go module", path)
	}
	out := c.output(p.PkgPath)
	if !slices.Contains(out.imports, path) {
		out.imports = append(out.imports, path)
	}
	return nil
}

func (c *compiler) function(fn *types.Func) error {
	src, ok := c.source.Functions[fn]
	if !ok {
		return fmt.Errorf("no Go source for %s", fn.FullName())
	}
	p, pos := src.Package, src.Decl.Pos()
	switch c.state[fn] {
	case 1:
		return load.Error(p, pos, "recursive call graph through %s", fn.Name())
	case 2:
		return nil
	}
	if src.Err != nil {
		return src.Err
	}
	c.state[fn] = 1
	sig := fn.Signature()
	if sig.Variadic() || sig.TypeParams().Len() != 0 || sig.Results().Len() != 1 || src.Decl.Body == nil {
		return load.Error(p, pos, "expected a concrete, non-variadic function with one result")
	}
	if sig.Recv() != nil && !valueReceiver(fn) {
		return load.Error(p, pos, "expected a concrete value receiver")
	}
	if sig.Results().At(0).Name() != "" {
		return load.Error(p, pos, "named results are unsupported")
	}
	out := c.output(p.PkgPath)
	f := function{
		compiler: c, source: src, fn: fn, locals: make(map[*types.Var]int),
		contracts: make(map[*types.Func]bool),
	}
	model := ir.Function{Symbol: symbol(fn), Termination: src.Termination}
	var bindings []ir.Binding
	var contracts []ir.Symbol
	params := make([]*types.Var, 0, sig.Params().Len()+1)
	if sig.Recv() != nil {
		params = append(params, sig.Recv())
	}
	for i := 0; i < sig.Params().Len(); i++ {
		params = append(params, sig.Params().At(i))
	}
	for _, param := range params {
		t, err := c.goType(p, pos, param.Type())
		if err != nil {
			return err
		}
		bindings = append(bindings, ir.Binding{ID: f.bind(param), Name: param.Name(), Type: t, Unused: param.Name() == "_" || param.Name() == ""})
	}
	var err error
	model.Result, err = c.goType(p, pos, sig.Results().At(0).Type())
	if err != nil {
		return err
	}
	if src.Termination != "" && len(src.Abstract) != 0 {
		return load.Error(p, pos, "measured recursion does not support caller-local contracts")
	}
	if len(src.Abstract) != 0 && len(src.Laws) == 0 {
		return load.Error(p, pos, "go-lean abstraction requires a verified root")
	}
	c.abstract[fn] = len(src.Abstract) != 0
	var calleeNames []string
	for _, target := range src.Abstract {
		callee := src.ResolveCallee(target)
		decl, found := c.source.Functions[callee]
		if !found || callee == fn || len(decl.Assumptions) == 0 {
			return load.Error(p, pos, "abstract callee %q must name another function with golean:assume laws", target)
		}
		if decl.Err != nil {
			return decl.Err
		}
		if _, exists := f.contracts[callee]; exists {
			return load.Error(p, pos, "duplicate abstract callee %q", target)
		}
		contract, err := f.contract(fn, callee, decl.Assumptions)
		if err != nil {
			return err
		}
		f.contracts[callee] = false
		contracts = append(contracts, symbol(callee))
		calleeNames = append(calleeNames, target)
		out.decls = append(out.decls, ir.NewDeclarationContract(contract))
	}
	model.Body, err = f.block(src.Decl.Body.List, func() (ir.Expr, error) {
		return ir.Expr{}, load.Error(p, pos, "supported function paths must return a value")
	})
	if err != nil {
		return err
	}
	if src.Termination != "" && !f.recursive {
		return load.Error(p, pos, "termination measure requires a direct recursive call")
	}
	for _, name := range calleeNames {
		if !f.contracts[src.ResolveCallee(name)] {
			return load.Error(p, pos, "unused abstract callee %q", name)
		}
	}
	model.Params = list(bindings)
	model.Contracts = list(contracts)
	for i, law := range src.Laws {
		for _, existing := range out.laws {
			if existing.Proposition.Name == law.Name {
				return load.Error(p, src.LawPositions[i], "duplicate package law %s", law.Name)
			}
		}
		out.laws = append(out.laws, ir.Law{Proposition: law, Caller: model.Symbol, Contracts: model.Contracts})
	}
	out.decls = append(out.decls, ir.NewDeclarationFunction(model))
	c.state[fn] = 2
	return nil
}

type function struct {
	*compiler
	source    load.Function
	fn        *types.Func
	recursive bool
	locals    map[*types.Var]int
	next      int
	contracts map[*types.Func]bool
}

func (f *function) bind(v *types.Var) int {
	id := f.next
	f.next++
	if v.Name() != "_" {
		f.locals[v] = id
	}
	return id
}

func (f *function) contract(caller, callee *types.Func, laws []ir.Proposition) (ir.Contract, error) {
	p, pos := f.source.Package, f.source.Decl.Pos()
	contract := ir.Contract{Caller: symbol(caller), Callee: symbol(callee), Assumptions: list(laws)}
	signature := callee.Signature()
	var params []ir.Type
	if signature.Recv() != nil || signature.Variadic() || signature.TypeParams().Len() != 0 || signature.Results().Len() != 1 {
		return contract, load.Error(p, pos, "abstract callee %s must have a scalar function signature", callee.Name())
	}
	scalar := func(typ types.Type) (ir.Type, error) {
		b, ok := typ.Underlying().(*types.Basic)
		if !ok {
			return ir.Type{}, load.Error(p, pos, "abstract callee %s requires scalar types", callee.Name())
		}
		return basic(p, pos, b)
	}
	for i := 0; i < signature.Params().Len(); i++ {
		t, err := scalar(signature.Params().At(i).Type())
		if err != nil {
			return contract, err
		}
		params = append(params, t)
	}
	var err error
	contract.Params = list(params)
	contract.Result, err = scalar(signature.Results().At(0).Type())
	return contract, err
}

type continuation func() (ir.Expr, error)

func endsWithReturn(stmts []ast.Stmt) bool {
	if len(stmts) == 0 {
		return false
	}
	switch last := stmts[len(stmts)-1].(type) {
	case *ast.ReturnStmt:
		return true
	case *ast.IfStmt:
		return endsWithReturn(last.Body.List) && elseReturns(last.Else)
	default:
		return false
	}
}

func elseReturns(branch ast.Stmt) bool {
	switch s := branch.(type) {
	case *ast.IfStmt:
		return endsWithReturn(s.Body.List) && elseReturns(s.Else)
	case *ast.BlockStmt:
		return endsWithReturn(s.List)
	default:
		return false
	}
}

func (f *function) block(stmts []ast.Stmt, tail continuation) (ir.Expr, error) {
	if len(stmts) == 0 {
		return tail()
	}
	p := f.source.Package
	statement := stmts[0]
	rest := func() (ir.Expr, error) { return f.block(stmts[1:], tail) }
	switch s := statement.(type) {
	case *ast.ReturnStmt:
		if len(s.Results) != 1 || len(stmts) != 1 {
			return ir.Expr{}, load.Error(p, s.Pos(), "expected a return with one value at the end of a block")
		}
		return f.expr(s.Results[0])
	case *ast.IfStmt:
		if s.Init != nil {
			return ir.Expr{}, load.Error(p, s.Pos(), "if initializers are unsupported")
		}
		cond, err := f.expr(s.Cond)
		if err != nil {
			return ir.Expr{}, err
		}
		var after ir.Expr
		var afterErr error
		join := !endsWithReturn(s.Body.List) && !elseReturns(s.Else)
		joinID := f.next
		if join {
			f.next++
		}
		shared := func() (ir.Expr, error) {
			if join {
				return ir.NewExprJump(ir.Jump{ID: joinID}), nil
			}
			if isMissing(after) && afterErr == nil {
				after, afterErr = rest()
			}
			return after, afterErr
		}
		yes, err := f.block(s.Body.List, shared)
		if err != nil {
			return ir.Expr{}, err
		}
		var no ir.Expr
		switch e := s.Else.(type) {
		case nil:
			no, err = shared()
		case *ast.BlockStmt:
			no, err = f.block(e.List, shared)
		case *ast.IfStmt:
			no, err = f.block([]ast.Stmt{e}, shared)
		}
		if err != nil {
			return ir.Expr{}, err
		}
		branch := ir.NewExprIf(ir.If{Cond: cond, Then: yes, Else: no})
		if join {
			next, err := rest()
			if err != nil {
				return ir.Expr{}, err
			}
			return ir.NewExprJoin(ir.Join{ID: joinID, Next: next, Body: branch}), nil
		}
		if isMissing(after) && len(stmts) > 1 {
			return ir.Expr{}, load.Error(p, stmts[1].Pos(), "unreachable statements after unconditional return")
		}
		return branch, nil
	case *ast.TypeSwitchStmt:
		return f.enumMatch(s, rest, len(stmts) > 1)
	case *ast.ForStmt, *ast.RangeStmt:
		return ir.Expr{}, load.Error(p, statement.Pos(), "raw loops are unsupported in modeled Go; use lean.FoldN, lean.FoldNUntil, lean.FoldList, or lean.FoldListUntil")
	case *ast.AssignStmt:
		if s.Tok != token.DEFINE || len(s.Lhs) != len(s.Rhs) {
			return ir.Expr{}, load.Error(p, s.Pos(), "only immutable short declarations with explicit values are supported")
		}
		var names []*ast.Ident
		for _, lhs := range s.Lhs {
			name, ok := lhs.(*ast.Ident)
			if !ok {
				return ir.Expr{}, load.Error(p, lhs.Pos(), "expected a local name")
			}
			names = append(names, name)
		}
		return f.bindings(names, s.Rhs, rest)
	case *ast.DeclStmt:
		d, ok := s.Decl.(*ast.GenDecl)
		if !ok || d.Tok != token.VAR || len(d.Specs) != 1 {
			return ir.Expr{}, load.Error(p, s.Pos(), "expected a single initialized local var declaration")
		}
		v := d.Specs[0].(*ast.ValueSpec)
		if len(v.Values) == 0 && len(v.Names) == 1 {
			obj := p.TypesInfo.Defs[v.Names[0]].(*types.Var)
			t, err := f.goType(p, v.Pos(), obj.Type())
			if err != nil {
				return ir.Expr{}, err
			}
			if t.Kind() == ir.EnumType {
				id := f.bind(obj)
				body, err := rest()
				return ir.NewExprLet(ir.Let{ID: id, Value: f.zero(t), Body: body}), err
			}
		}
		return f.bindings(v.Names, v.Values, rest)
	default:
		return ir.Expr{}, load.Error(p, s.Pos(), "unsupported statement %T", s)
	}
}

func (f *function) bindings(names []*ast.Ident, values []ast.Expr, tail continuation) (ir.Expr, error) {
	p := f.source.Package
	if len(names) != len(values) {
		return ir.Expr{}, load.Error(p, names[0].Pos(), "local bindings require individual initializers")
	}
	bindings := make([]ir.Let, len(names))
	for i, name := range names {
		v, ok := p.TypesInfo.Defs[name].(*types.Var)
		if !ok {
			return ir.Expr{}, load.Error(p, name.Pos(), "reassignment is unsupported")
		}
		value, err := f.expr(values[i])
		if err != nil {
			return ir.Expr{}, err
		}
		if _, err := f.goType(p, name.Pos(), v.Type()); err != nil {
			return ir.Expr{}, err
		}
		bindings[i] = ir.Let{ID: f.bind(v), Value: value}
	}
	body, err := tail()
	if err != nil {
		return ir.Expr{}, err
	}
	for i := len(bindings) - 1; i >= 0; i-- {
		bindings[i].Body = body
		body = ir.NewExprLet(bindings[i])
	}
	return body, nil
}
