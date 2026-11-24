package lower

import (
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

func (c *compiler) enumType(p loaded.Package, pos string, obj loaded.ObjectID, enum loaded.Enum) (ir.Type, error) {
	id := c.symbol(obj)
	if err := c.depend(p, id.Package, pos); err != nil {
		return ir.Type{}, err
	}
	if c.state[obj] == 0 {
		owner := c.inputPackage(id.Package)
		if err := c.checkEnumZero(obj); err != nil {
			return ir.Type{}, err
		}
		c.state[obj] = 1
		result := ir.Enum{Symbol: id}
		var variants []ir.Field
		for _, payload := range values(enum.Payloads) {
			t, err := c.goType(owner, c.object(payload).Pos, c.object(payload).Type)
			if err != nil {
				return ir.Type{}, err
			}
			if c.object(payload).Name == enum.Default {
				result.Default = len(variants)
			}
			variants = append(variants, ir.Field{Name: c.object(payload).Name, Type: t})
		}
		result.Variants = list(variants)
		out := c.output(id.Package)
		out.decls = append(out.decls, ir.NewDeclarationEnum(result))
		c.state[obj] = 2
	}
	return ir.NewTypeEnumTypeRef(ir.EnumTypeRef{Symbol: id}), nil
}

func (c *compiler) checkEnumZero(obj loaded.ObjectID) error {
	states := make(map[loaded.ObjectID]int)
	var path []string
	var visit func(loaded.TypeID) error
	visit = func(id loaded.TypeID) error {
		named := c.unalias(id)
		if named.Kind != loaded.NamedType {
			return nil
		}
		name := named.Object
		entry := c.object(name)
		if entry.Package == loaded.Curated {
			if entry.Name == "FoldControl" {
				return visit(at(named.Args, uint(0)))
			}
			return nil
		}
		if states[name] == 1 {
			return diagnostic(c.object(obj).Pos, "cyclic enum zero value: %s", strings.Join(append(path, entry.Name), " -> "))
		}
		if states[name] == 2 {
			return nil
		}
		states[name] = 1
		path = append(path, entry.Name)
		if entry.Enum.IsSome() {
			enum := entry.Enum.UnwrapOr(loaded.Enum{})
			for _, payload := range values(enum.Payloads) {
				variant := c.object(payload)
				if variant.Name == enum.Default {
					if err := visit(variant.Type); err != nil {
						return err
					}
				}
			}
		} else if record := c.inputType(named.Underlying); record.Kind == loaded.StructType {
			for _, field := range values(record.Fields) {
				if err := visit(c.object(field).Type); err != nil {
					return err
				}
			}
		}
		path = path[:len(path)-1]
		states[name] = 2
		return nil
	}
	return visit(c.object(obj).Type)
}

func (f *function) enumMatch(pos string, stmt loaded.SwitchStmt, rest continuation, trailing bool) (ir.Expr, error) {
	p := f.pkg
	method := f.object(stmt.CaseMethod)
	if err := subsetError(stmt.ValidateCaseMethod(method, pos)); err != nil {
		return ir.Expr{}, err
	}
	obj := f.object(method.EnumCase)
	enum := obj.Enum.UnwrapOr(loaded.Enum{})
	if _, err := f.goType(p, pos, obj.Type); err != nil {
		return ir.Expr{}, err
	}
	value, err := f.expr(stmt.Receiver)
	if err != nil {
		return ir.Expr{}, err
	}
	var cases []ir.MatchCase
	remaining := make(map[loaded.ObjectID]bool)
	for _, variant := range values(enum.Payloads) {
		remaining[variant] = true
	}
	join := f.next
	f.next++
	continued := false
	shared := func() (ir.Expr, error) {
		continued = true
		return ir.NewExprJump(ir.Jump{ID: join}), nil
	}
	for _, clause := range values(stmt.Cases) {
		if err := subsetError(clause.Validate()); err != nil {
			return ir.Expr{}, err
		}
		if !remaining[clause.Variant] {
			return ir.Expr{}, diagnostic(clause.Pos, "expected an unhandled enum payload type")
		}
		delete(remaining, clause.Variant)
		binding := clause.Binding
		id := -1
		if binding != 0 {
			id = f.bind(binding)
		}
		body, err := f.block(values(clause.Body), shared)
		delete(f.locals, binding)
		if err != nil {
			return ir.Expr{}, err
		}
		cases = append(cases, ir.MatchCase{Variant: f.object(clause.Variant).Name, Binding: id, Body: body})
	}
	for _, variant := range values(enum.Payloads) {
		if remaining[variant] {
			return ir.Expr{}, diagnostic(pos, "non-exhaustive enum switch, missing %s", f.object(variant).Name)
		}
	}
	var sequence ir.MatchSeq
	for i := len(cases) - 1; i >= 0; i-- {
		sequence = ir.MatchSeq{First: lean.NewBox(ir.MatchSeqItem{Value: cases[i], Rest: sequence})}
	}
	result := ir.NewExprMatch(ir.Match{Value: value, Cases: sequence})
	// Go still requires a trailing return for an exhaustive type switch.
	// Check it even when all cases return so it cannot hide unsupported code.
	if continued || trailing {
		next, err := rest()
		if err != nil {
			return ir.Expr{}, err
		}
		if continued {
			return ir.NewExprJoin(ir.Join{ID: join, Next: next, Body: result}), nil
		}
	}
	return result, nil
}
