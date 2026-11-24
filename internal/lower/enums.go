package lower

import (
	"go/ast"
	"go/token"
	"go/types"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"golang.org/x/tools/go/packages"
)

func (c *compiler) enumType(p *packages.Package, pos token.Pos, obj *types.TypeName, enum load.Enum) (ir.Type, error) {
	id := symbol(obj)
	if err := c.depend(p, id.Package, pos); err != nil {
		return ir.Type{}, err
	}
	if c.state[obj] == 0 {
		owner := c.source.Packages[id.Package]
		if err := c.checkEnumZero(owner, obj); err != nil {
			return ir.Type{}, err
		}
		c.state[obj] = 1
		result := ir.Enum{Symbol: id}
		for _, payload := range enum.Payloads {
			t, err := c.goType(owner, payload.Pos(), payload.Type())
			if err != nil {
				return ir.Type{}, err
			}
			if payload.Name() == enum.Spec.Default {
				result.Default = len(result.Variants)
			}
			result.Variants = append(result.Variants, ir.Field{Name: payload.Name(), Type: t})
		}
		out := c.output(id.Package)
		out.Decls = append(out.Decls, result)
		c.state[obj] = 2
	}
	return ir.Type{Kind: ir.EnumType, Record: id}, nil
}

func (c *compiler) checkEnumZero(p *packages.Package, obj *types.TypeName) error {
	states := make(map[*types.TypeName]int)
	var path []string
	var visit func(types.Type) error
	visit = func(t types.Type) error {
		named, ok := types.Unalias(t).(*types.Named)
		if !ok {
			return nil
		}
		name := named.Obj()
		if name.Pkg() != nil && name.Pkg().Path() == load.Curated {
			if name.Name() == "FoldControl" {
				return visit(named.TypeArgs().At(0))
			}
			return nil
		}
		if states[name] == 1 {
			return load.Error(p, obj.Pos(), "cyclic enum zero value: %s", strings.Join(append(path, name.Name()), " -> "))
		}
		if states[name] == 2 {
			return nil
		}
		states[name] = 1
		path = append(path, name.Name())
		if enum, ok := c.source.Enums[name]; ok {
			for _, payload := range enum.Payloads {
				if payload.Name() == enum.Spec.Default {
					if err := visit(payload.Type()); err != nil {
						return err
					}
				}
			}
		} else if record, ok := named.Underlying().(*types.Struct); ok {
			for field := range record.Fields() {
				if err := visit(field.Type()); err != nil {
					return err
				}
			}
		}
		path = path[:len(path)-1]
		states[name] = 2
		return nil
	}
	return visit(obj.Type())
}

func (f *function) enumMatch(stmt *ast.TypeSwitchStmt, rest continuation, trailing bool) (ir.Expr, error) {
	p := f.source.Package
	info := p.TypesInfo
	invalid := func() (ir.Expr, error) {
		return nil, load.Error(p, stmt.Pos(), "expected a type switch on enum.Case() without an initializer")
	}
	if stmt.Init != nil {
		return invalid()
	}
	var assertionExpr ast.Expr
	switch assign := stmt.Assign.(type) {
	case *ast.AssignStmt:
		if assign.Tok != token.DEFINE || len(assign.Rhs) != 1 {
			return invalid()
		}
		assertionExpr = assign.Rhs[0]
	case *ast.ExprStmt:
		assertionExpr = assign.X
	}
	assertion, ok := assertionExpr.(*ast.TypeAssertExpr)
	if !ok {
		return invalid()
	}
	call, ok := assertion.X.(*ast.CallExpr)
	if !ok || len(call.Args) != 0 {
		return invalid()
	}
	selector, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		return invalid()
	}
	sel := info.Selections[selector]
	if sel == nil || sel.Kind() != types.MethodVal || sel.Indirect() || len(sel.Index()) != 1 {
		return invalid()
	}
	fn := sel.Obj().(*types.Func)
	owner := f.compiler.source.EnumCases[fn]
	if owner == nil {
		return invalid()
	}
	enum := f.compiler.source.Enums[owner]
	if _, err := f.goType(p, stmt.Pos(), owner.Type()); err != nil {
		return nil, err
	}
	value, err := f.expr(selector.X)
	if err != nil {
		return nil, err
	}
	result := ir.Match{Value: value}
	remaining := make(map[*types.TypeName]bool)
	for _, variant := range enum.Payloads {
		remaining[variant] = true
	}
	join := f.next
	f.next++
	continued := false
	shared := func() (ir.Expr, error) {
		continued = true
		return ir.Jump{ID: join}, nil
	}
	for _, node := range stmt.Body.List {
		clause := node.(*ast.CaseClause)
		if len(clause.List) != 1 {
			return nil, load.Error(p, clause.Pos(), "enum switches require exactly one variant per case and no default")
		}
		typ, ok := types.Unalias(info.TypeOf(clause.List[0])).(*types.Named)
		if !ok || !remaining[typ.Obj()] {
			return nil, load.Error(p, clause.Pos(), "expected an unhandled enum payload type")
		}
		delete(remaining, typ.Obj())
		binding, bound := info.Implicits[clause].(*types.Var)
		id := -1
		if bound {
			id = f.bind(binding)
		}
		body, err := f.block(clause.Body, shared)
		delete(f.locals, binding)
		if err != nil {
			return nil, err
		}
		result.Cases = append(result.Cases, ir.MatchCase{Variant: typ.Obj().Name(), Binding: id, Body: body})
	}
	for _, variant := range enum.Payloads {
		if remaining[variant] {
			return nil, load.Error(p, stmt.Pos(), "non-exhaustive enum switch, missing %s", variant.Name())
		}
	}
	// Go still requires a trailing return for an exhaustive type switch.
	// Check it even when all cases return so it cannot hide unsupported code.
	if continued || trailing {
		next, err := rest()
		if err != nil {
			return nil, err
		}
		if continued {
			return ir.Join{ID: join, Next: next, Body: result}, nil
		}
	}
	return result, nil
}
