package lower

import (
	"go/ast"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"golang.org/x/tools/go/packages"
)

func (c *compiler) enumType(p *packages.Package, pos token.Pos, obj *types.TypeName, e load.Enum) (ir.Type, error) {
	id := symbol(obj)
	t := ir.Type{Kind: ir.EnumType, Record: id}
	if err := c.depend(p, id.Package, pos); err != nil {
		return t, err
	}
	if c.state[obj] != 0 {
		return t, nil
	}
	c.state[obj] = 1
	owner := c.source.Packages[id.Package]
	d := ir.Enum{Symbol: id}
	for _, variant := range e.Variants {
		v := obj.Pkg().Scope().Lookup(variant).Type().Underlying().(*types.Struct)
		constructor := ir.Variant{Name: variant}
		for i := range v.NumFields() {
			field := v.Field(i)
			ft, err := c.goType(owner, field.Pos(), field.Type())
			if err != nil {
				return t, err
			}
			constructor.Fields = append(constructor.Fields, ir.Field{Name: field.Name(), Type: ft})
		}
		d.Variants = append(d.Variants, constructor)
	}
	out := c.output(id.Package)
	out.Decls = append(out.Decls, d)
	c.state[obj] = 2
	return t, nil
}

func (f *function) enumCall(e *ast.CallExpr, fn *types.Func) (ir.Expr, bool, error) {
	p := f.source.Package
	callee := f.compiler.source.Functions[fn]
	if !callee.Generated {
		return nil, false, nil
	}
	for _, enum := range f.compiler.source.Enums[fn.Pkg().Path()] {
		if fn.Name() == enum.Matcher() {
			target, err := f.expr(e.Args[0])
			if err != nil {
				return nil, true, err
			}
			model := ir.Match{Target: target}
			for i, variant := range enum.Variants {
				callback, ok := e.Args[i+1].(*ast.FuncLit)
				if !ok {
					return nil, true, load.Error(p, e.Args[i+1].Pos(), "enum matching requires inline callbacks")
				}
				param := p.TypesInfo.TypeOf(callback).(*types.Signature).Params().At(0)
				branch, err := f.variantBranch(variant, param, callback.Body.List)
				if err != nil {
					return nil, true, err
				}
				model.Branches = append(model.Branches, branch)
			}
			return model, true, nil
		}
		for _, variant := range enum.Variants {
			if fn.Name() == enum.Constructor(variant) {
				t, err := f.goType(p, e.Pos(), p.TypesInfo.TypeOf(e))
				if err != nil {
					return nil, true, err
				}
				args, err := f.arguments(e.Args)
				return ir.EnumLiteral{Type: t.Record, Variant: variant, Fields: args}, true, err
			}
		}
	}
	return nil, false, nil
}

type variantField struct {
	id   int
	used bool
}

func (f *function) variantBranch(name string, param *types.Var, body []ast.Stmt) (ir.MatchBranch, error) {
	p := f.source.Package
	branch := ir.MatchBranch{Variant: name}
	fields := param.Type().Underlying().(*types.Struct)
	locals := make(map[string]*variantField)
	for i := range fields.NumFields() {
		id := f.next
		f.next++
		locals[fields.Field(i).Name()] = &variantField{id: id}
		branch.Bindings = append(branch.Bindings, id)
	}
	if f.variantLocals == nil {
		f.variantLocals = make(map[*types.Var]map[string]*variantField)
	}
	f.variantLocals[param] = locals
	defer delete(f.variantLocals, param)
	f.structural++
	defer func() { f.structural-- }()
	var err error
	branch.Body, err = f.block(body, func() (ir.Expr, error) {
		return nil, load.Error(p, param.Pos(), "enum branch must return a value")
	})
	for _, field := range locals {
		if !field.used {
			for i, id := range branch.Bindings {
				if id == field.id {
					branch.Bindings[i] = -1
					break
				}
			}
		}
	}
	return branch, err
}

func (f *function) enumSwitch(s *ast.TypeSwitchStmt, rest []ast.Stmt) (ir.Expr, error) {
	p := f.source.Package
	fail := func(message string) (ir.Expr, error) { return nil, load.Error(p, s.Pos(), "%s", message) }
	assign, ok := s.Assign.(*ast.AssignStmt)
	if s.Init != nil || !ok || len(rest) != 0 {
		return fail("expected a terminal enum switch with a named case value")
	}
	assertion := assign.Rhs[0].(*ast.TypeAssertExpr)
	selector, ok := assertion.X.(*ast.SelectorExpr)
	if !ok || selector.Sel.Name != "variant" {
		return fail("expected a switch over an enum discriminator")
	}
	name, ok := p.TypesInfo.TypeOf(selector.X).(*types.Named)
	if !ok {
		return fail("expected a switch over an enum discriminator")
	}
	var enum load.Enum
	for _, candidate := range f.compiler.source.Enums[name.Obj().Pkg().Path()] {
		if candidate.Name == name.Obj().Name() {
			enum = candidate
			break
		}
	}
	if enum.Name == "" {
		return fail("expected a switch over an enum discriminator")
	}
	target, err := f.expr(selector.X)
	if err != nil {
		return nil, err
	}
	remaining := make(map[string]bool)
	for _, variant := range enum.Variants {
		remaining[variant] = true
	}
	model := ir.Match{Target: target}
	for _, statement := range s.Body.List {
		clause := statement.(*ast.CaseClause)
		if len(clause.List) == 0 {
			if !panicOnly(p.TypesInfo, clause.Body) {
				return fail("enum switch default must contain only panic")
			}
			continue
		}
		if len(clause.List) != 1 {
			return fail("enum switch cases require one value variant each")
		}
		variant, ok := p.TypesInfo.TypeOf(clause.List[0]).(*types.Named)
		if !ok || variant.Obj().Pkg() != name.Obj().Pkg() || !remaining[variant.Obj().Name()] {
			return fail("enum switch case must name an uncovered value variant")
		}
		delete(remaining, variant.Obj().Name())
		param := p.TypesInfo.Implicits[clause].(*types.Var)
		branch, err := f.variantBranch(variant.Obj().Name(), param, clause.Body)
		if err != nil {
			return nil, err
		}
		model.Branches = append(model.Branches, branch)
	}
	if len(remaining) != 0 {
		return fail("enum switch must cover every variant")
	}
	return model, nil
}

func panicOnly(info *types.Info, body []ast.Stmt) bool {
	if len(body) != 1 {
		return false
	}
	stmt, ok := body[0].(*ast.ExprStmt)
	if !ok {
		return false
	}
	call, ok := stmt.X.(*ast.CallExpr)
	if !ok || len(call.Args) != 1 {
		return false
	}
	id, ok := call.Fun.(*ast.Ident)
	return ok && info.Uses[id] == types.Universe.Lookup("panic")
}
