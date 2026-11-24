// Package lower validates the supported Go subset and builds typed IR.
package lower

import (
	"fmt"
	"slices"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

type compiler struct {
	source   loaded.Program
	packages map[string]*packageBuilder
	state    map[loaded.ObjectID]uint8
	abstract map[loaded.ObjectID]bool
	pending  []string
}

func Program(source loaded.Program) ([]*ir.Package, error) {
	c := compiler{
		source:   source,
		packages: make(map[string]*packageBuilder),
		state:    make(map[loaded.ObjectID]uint8),
		abstract: make(map[loaded.ObjectID]bool),
	}
	for _, path := range values(source.SelectedPackages) {
		c.output(path)
	}
	for i := 0; i < len(c.pending); i++ {
		path := c.pending[i]
		p := c.inputPackage(path)
		for _, decl := range values(p.Declarations) {
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
		if issue := c.inputPackage(p.Path).Issue; issue != "" {
			return nil, fmt.Errorf("%s", issue)
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

func values[T any](array lean.Array[T]) []T {
	result := make([]T, array.Size())
	for i := range result {
		result[i] = at(array, uint(i))
	}
	return result
}

func at[T any, I ~uint](array lean.Array[T], index I) T {
	var zero T
	return array.Get(uint(index)).UnwrapOr(zero)
}

func (c *compiler) inputPackage(path string) loaded.Package {
	return c.source.Packages.Find(path).UnwrapOr(loaded.Package{})
}

func (c *compiler) object(id loaded.ObjectID) loaded.Object {
	return c.source.LookupObject(id).UnwrapOr(loaded.Object{})
}

func (c *compiler) inputType(id loaded.TypeID) loaded.Type {
	return c.source.LookupType(id).UnwrapOr(loaded.Type{})
}

func (c *compiler) inputStatement(id loaded.StmtID) loaded.Statement {
	return c.source.LookupStatement(id).UnwrapOr(loaded.Statement{})
}

func diagnostic(pos, message string, args ...any) error {
	return fmt.Errorf("%s: %s", pos, fmt.Sprintf(message, args...))
}

func (c *compiler) declaration(p loaded.Package, decl loaded.Declaration) error {
	pos := decl.Pos
	obj := c.object(decl.Object)
	switch obj.Kind {
	case loaded.FunctionObject:
		if (obj.Name == "init" && c.inputType(obj.Type).Receiver == 0) || obj.Name == "_" {
			return diagnostic(pos, "unsupported function declaration %s", obj.Name)
		}
		return c.function(decl.Object)
	case loaded.TypeName:
		typ := c.inputType(obj.Type)
		if typ.Kind == loaded.AliasType && typ.Generic {
			return diagnostic(pos, "unsupported generic type alias %s", obj.Name)
		}
		t, err := c.goType(p, pos, obj.Type)
		if err != nil {
			return err
		}
		if obj.Name != "_" && ((t.Kind() != ir.Record && t.Kind() != ir.EnumType) || typ.Kind == loaded.AliasType) {
			out := c.output(p.Path)
			out.decls = append(out.decls, ir.NewDeclarationTypeAlias(ir.TypeAlias{Symbol: c.symbol(decl.Object), Type: t}))
		}
	case loaded.ConstantObject:
		t, err := c.goType(p, pos, obj.DefaultType)
		if err != nil {
			return err
		}
		if obj.Value.Integer && !obj.Value.FitsScalar(c.underlying(obj.DefaultType).Scalar(p.WordBits)) {
			return diagnostic(pos, "constant %s is not representable as %s", obj.Name, c.inputType(obj.DefaultType).Display)
		}
		if obj.Name != "_" {
			out := c.output(p.Path)
			out.decls = append(out.decls, ir.NewDeclarationNamedConstant(ir.NamedConstant{Symbol: c.symbol(decl.Object), Value: ir.Constant{Type: t, Value: obj.Value.Value}}))
		}
	case loaded.Variable:
		return diagnostic(pos, "package variables are unsupported in modeled Go")
	default:
		return diagnostic(pos, "unsupported package declaration")
	}
	return nil
}

func (c *compiler) symbol(id loaded.ObjectID) ir.Symbol {
	obj := c.object(id)
	name := obj.Name
	if obj.Kind == loaded.FunctionObject {
		if receiver := c.inputType(obj.Type).Receiver; receiver != 0 {
			typ := c.unalias(c.object(receiver).Type)
			name = c.object(typ.Object).Name + "$" + name
		}
	}
	return ir.Symbol{Package: obj.Package, Name: name}
}

type packageBuilder struct {
	ir.Package
	imports, leanImports []string
	decls                []ir.Declaration
	laws                 []ir.Law
}

func propositions(laws []loaded.Proposition) []ir.Proposition {
	result := make([]ir.Proposition, len(laws))
	for i, law := range laws {
		result[i] = ir.Proposition(law)
	}
	return result
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
	source := c.inputPackage(path)
	p := &packageBuilder{Package: ir.Package{Path: path, Name: source.Name, Dir: source.Dir}}
	p.leanImports = values(source.LeanImports)
	slices.Sort(p.leanImports)
	p.leanImports = slices.Compact(p.leanImports)
	if laws := values(source.Laws); len(laws) != 0 {
		for _, law := range laws {
			p.laws = append(p.laws, ir.Law{Proposition: ir.Proposition(law)})
		}
	}
	p.Word = ir.UInt64
	if source.WordBits == 32 {
		p.Word = ir.UInt32
	}
	c.packages[path] = p
	if source.Modeled {
		c.pending = append(c.pending, path)
	}
	return p
}

func (c *compiler) depend(p loaded.Package, path, pos string) error {
	if p.Path == path {
		return nil
	}
	target := c.inputPackage(path)
	if target.Issue != "" {
		return fmt.Errorf("%s", target.Issue)
	}
	if p.Module == "" || target.Module != p.Module {
		return diagnostic(pos, "concrete dependency %s must be in the same Go module", path)
	}
	out := c.output(p.Path)
	if !slices.Contains(out.imports, path) {
		out.imports = append(out.imports, path)
	}
	return nil
}

func (c *compiler) function(fn loaded.ObjectID) error {
	obj := c.object(fn)
	if !obj.Function.IsSome() {
		return fmt.Errorf("no Go source for %s", obj.FullName)
	}
	src := obj.Function.UnwrapOr(loaded.Function{})
	p, pos := c.inputPackage(obj.Package), src.Pos
	switch c.state[fn] {
	case 1:
		return diagnostic(pos, "recursive call graph through %s", obj.Name)
	case 2:
		return nil
	}
	if src.Issue != "" {
		return fmt.Errorf("%s", src.Issue)
	}
	c.state[fn] = 1
	sig := c.inputType(obj.Type)
	if err := subsetError(src.ValidateSignature(sig, c.object(at(sig.Results, uint(0))))); err != nil {
		return err
	}
	out := c.output(p.Path)
	f := function{
		compiler: c, source: src, pkg: p, fn: fn, locals: make(map[loaded.ObjectID]int),
		contracts: make(map[loaded.ObjectID]bool),
	}
	model := ir.Function{Symbol: c.symbol(fn), Termination: src.Termination}
	var bindings []ir.Binding
	var contracts []ir.Symbol
	params := values(sig.Params)
	if sig.Receiver != 0 {
		params = append([]loaded.ObjectID{sig.Receiver}, params...)
	}
	for _, id := range params {
		param := c.object(id)
		t, err := c.goType(p, pos, param.Type)
		if err != nil {
			return err
		}
		bindings = append(bindings, ir.Binding{ID: f.bind(id), Name: param.Name, Type: t, Unused: param.Name == "_" || param.Name == ""})
	}
	var err error
	model.Result, err = c.goType(p, pos, c.object(at(sig.Results, uint(0))).Type)
	if err != nil {
		return err
	}
	if src.Termination != "" && src.Abstract.Size() != 0 {
		return diagnostic(pos, "measured recursion does not support caller-local contracts")
	}
	if src.Abstract.Size() != 0 && src.Laws.Size() == 0 {
		return diagnostic(pos, "go-lean abstraction requires a verified root")
	}
	c.abstract[fn] = src.Abstract.Size() != 0
	for _, target := range values(src.Abstract) {
		callee := target.Object
		decl := c.object(callee).Function.UnwrapOr(loaded.Function{})
		if callee == 0 || callee == fn || decl.Assumptions.Size() == 0 {
			return diagnostic(pos, "abstract callee %q must name another function with golean:assume laws", target.Name)
		}
		if decl.Issue != "" {
			return fmt.Errorf("%s", decl.Issue)
		}
		if _, exists := f.contracts[callee]; exists {
			return diagnostic(pos, "duplicate abstract callee %q", target.Name)
		}
		contract, err := f.contract(fn, callee, values(decl.Assumptions))
		if err != nil {
			return err
		}
		f.contracts[callee] = false
		contracts = append(contracts, c.symbol(callee))
		out.decls = append(out.decls, ir.NewDeclarationContract(contract))
	}
	model.Body, err = f.block(values(src.Body), func() (ir.Expr, error) {
		return ir.Expr{}, diagnostic(pos, "supported function paths must return a value")
	})
	if err != nil {
		return err
	}
	if src.Termination != "" && !f.recursive {
		return diagnostic(pos, "termination measure requires a direct recursive call")
	}
	for _, target := range values(src.Abstract) {
		if !f.contracts[target.Object] {
			return diagnostic(pos, "unused abstract callee %q", target.Name)
		}
	}
	model.Params = list(bindings)
	model.Contracts = list(contracts)
	for i, law := range values(src.Laws) {
		for _, existing := range out.laws {
			if existing.Proposition.Name == law.Name {
				return diagnostic(at(src.LawPositions, uint(i)), "duplicate package law %s", law.Name)
			}
		}
		out.laws = append(out.laws, ir.Law{Proposition: ir.Proposition(law), Caller: model.Symbol, Contracts: model.Contracts})
	}
	out.decls = append(out.decls, ir.NewDeclarationFunction(model))
	c.state[fn] = 2
	return nil
}

type function struct {
	*compiler
	source    loaded.Function
	pkg       loaded.Package
	fn        loaded.ObjectID
	recursive bool
	locals    map[loaded.ObjectID]int
	next      int
	contracts map[loaded.ObjectID]bool
}

func (f *function) bind(v loaded.ObjectID) int {
	id := f.next
	f.next++
	if f.object(v).Name != "_" {
		f.locals[v] = id
	}
	return id
}

func (f *function) contract(caller, callee loaded.ObjectID, laws []loaded.Proposition) (ir.Contract, error) {
	p, pos := f.pkg, f.source.Pos
	contract := ir.Contract{Caller: f.symbol(caller), Callee: f.symbol(callee), Assumptions: list(propositions(laws))}
	obj := f.object(callee)
	signature := f.inputType(obj.Type)
	var params []ir.Type
	if signature.Receiver != 0 || signature.Variadic || signature.Generic || signature.Results.Size() != 1 {
		return contract, diagnostic(pos, "abstract callee %s must have a scalar function signature", obj.Name)
	}
	scalar := func(id loaded.ObjectID) (ir.Type, error) {
		b := f.underlying(f.object(id).Type)
		if b.Kind != loaded.BasicType {
			return ir.Type{}, diagnostic(pos, "abstract callee %s requires scalar types", obj.Name)
		}
		return basic(p, pos, b)
	}
	for _, param := range values(signature.Params) {
		t, err := scalar(param)
		if err != nil {
			return contract, err
		}
		params = append(params, t)
	}
	contract.Params = list(params)
	var err error
	contract.Result, err = scalar(at(signature.Results, uint(0)))
	return contract, err
}

type continuation func() (ir.Expr, error)

func (c *compiler) endsWithReturn(stmts lean.Array[loaded.StmtID]) bool {
	if stmts.Size() == 0 {
		return false
	}
	last := c.inputStatement(at(stmts, stmts.Size()-1))
	switch form := last.Form.Case().(type) {
	case loaded.ReturnStmt:
		return true
	case loaded.IfStmt:
		return c.endsWithReturn(form.Then) && c.endsWithReturn(form.Else)
	}
	return false
}

func (f *function) block(stmts []loaded.StmtID, tail continuation) (ir.Expr, error) {
	if len(stmts) == 0 {
		return tail()
	}
	s := f.inputStatement(stmts[0])
	if err := subsetError(s.Validate()); err != nil {
		return ir.Expr{}, err
	}
	rest := func() (ir.Expr, error) { return f.block(stmts[1:], tail) }
	switch form := s.Form.Case().(type) {
	case loaded.ReturnStmt:
		if err := subsetError(form.ValidatePosition(s.Pos, len(stmts) == 1)); err != nil {
			return ir.Expr{}, err
		}
		return f.expr(at(form.Values, uint(0)))
	case loaded.IfStmt:
		cond, err := f.expr(form.Condition)
		if err != nil {
			return ir.Expr{}, err
		}
		var after ir.Expr
		var afterErr error
		join := !f.endsWithReturn(form.Then) && !f.endsWithReturn(form.Else)
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
		yes, err := f.block(values(form.Then), shared)
		if err != nil {
			return ir.Expr{}, err
		}
		no, err := f.block(values(form.Else), shared)
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
			return ir.Expr{}, diagnostic(f.inputStatement(stmts[1]).Pos, "unreachable statements after unconditional return")
		}
		return branch, nil
	case loaded.SwitchStmt:
		return f.enumMatch(s.Pos, form, rest, len(stmts) > 1)
	case loaded.ShortDecl:
		return f.bindings(values(form.Names), values(form.Values), rest)
	case loaded.VarDecl:
		if form.ZeroType != 0 {
			t, err := f.goType(f.pkg, form.ZeroTypePos, form.ZeroType)
			if err != nil {
				return ir.Expr{}, err
			}
			if t.Kind() == ir.EnumType {
				id := f.bind(at(form.Names, uint(0)).Object)
				body, err := rest()
				return ir.NewExprLet(ir.Let{ID: id, Value: f.zero(t), Body: body}), err
			}
		}
		return f.bindings(values(form.Names), values(form.Values), rest)
	}
	panic("unknown loaded statement")
}

func (f *function) bindings(names []loaded.Binding, values []loaded.ExprID, tail continuation) (ir.Expr, error) {
	p := f.pkg
	if len(names) != len(values) {
		return ir.Expr{}, diagnostic(names[0].Pos, "local bindings require individual initializers")
	}
	bindings := make([]ir.Let, len(names))
	for i, name := range names {
		v := f.object(name.Object)
		if v.Kind != loaded.Variable {
			return ir.Expr{}, diagnostic(name.Pos, "reassignment is unsupported")
		}
		value, err := f.expr(values[i])
		if err != nil {
			return ir.Expr{}, err
		}
		if _, err := f.goType(p, name.Pos, v.Type); err != nil {
			return ir.Expr{}, err
		}
		bindings[i] = ir.Let{ID: f.bind(name.Object), Value: value}
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
