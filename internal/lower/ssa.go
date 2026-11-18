// Package lower converts checked SSA into structured Lean-ready IR.
package lower

import (
	"go/constant"
	"go/token"
	"go/types"
	"net/url"
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/subset"
	"golang.org/x/tools/go/ssa"
)

func FromSSA(checked subset.Checked, sourceStem string, wordBits int64) ir.Program {
	var program ir.Program
	file := url.PathEscape(sourceStem)
	// The checker orders callees before callers, so their effects are already known.
	effects := make(map[*ssa.Function]bool)
	for _, fn := range checked.Functions() {
		l := lowerer{root: checked.Root(), file: file, bindings: make(map[ssa.Value]ir.Binder), effects: effects}
		result := ir.Function{Symbol: l.symbol(fn), Result: l.valueType(fn.Signature.Results().At(0).Type())}
		for _, param := range fn.Params {
			result.Params = append(result.Params, l.bind(param))
		}
		result.Body = l.body(fn.Blocks[0], nil)
		if l.usesWord {
			program.WordBits = wordBits
		}
		result.CanPanic = l.canPanic
		effects[fn] = result.CanPanic
		program.Functions = append(program.Functions, result)
	}
	return program
}

type lowerer struct {
	root     *ssa.Package
	file     string
	bindings map[ssa.Value]ir.Binder
	effects  map[*ssa.Function]bool
	canPanic bool
	next     int
	usesWord bool
}

func (l *lowerer) symbol(fn *ssa.Function) ir.Symbol {
	symbol := ir.Symbol{Package: l.root.Pkg.Path(), File: l.file, Name: fn.Name()}
	if fn.Pkg != l.root {
		symbol.Dependency = fn.Pkg.Pkg.Path()
	}
	return symbol
}

func (l *lowerer) bind(value ssa.Value) ir.Binder {
	binder := ir.Binder{Name: value.Name(), Index: l.next, Type: l.valueType(value.Type())}
	l.next++
	l.bindings[value] = binder
	return binder
}

func (l *lowerer) body(block, predecessor *ssa.BasicBlock) ir.Body {
	var result ir.Body
	for _, ins := range block.Instrs {
		switch ins := ins.(type) {
		case *ssa.BinOp:
			canPanic := ins.Op == token.QUO
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins), Value: l.binary(ins), CanPanic: canPanic,
			})
			l.canPanic = l.canPanic || canPanic
		case *ssa.UnOp:
			operand := l.value(ins.X)
			var value ir.Expr = ir.Negate{Value: operand}
			if ins.Op == token.NOT {
				value = ir.Not{Value: operand}
			}
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins), Value: value,
			})
		case *ssa.Call:
			target := ins.Call.StaticCallee()
			call := ir.Call{Callee: l.symbol(target)}
			for _, arg := range ins.Call.Args {
				call.Args = append(call.Args, l.value(arg))
			}
			canPanic := l.effects[target]
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins), Value: call, CanPanic: canPanic,
			})
			l.canPanic = l.canPanic || canPanic
		case *ssa.Convert:
			binder := l.bind(ins)
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: binder, Value: ir.Convert{Value: l.value(ins.X), To: binder.Type},
			})
		case *ssa.If:
			result.Result = ir.If{
				Condition: l.value(ins.Cond),
				Then:      l.body(block.Succs[0], block),
				Else:      l.body(block.Succs[1], block),
			}
		case *ssa.Phi:
			// Each branch contains only the computations along its own path.
			edge := ins.Edges[slices.Index(block.Preds, predecessor)]
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: l.value(edge)})
		case *ssa.Return:
			result.Result = ir.Return{Value: l.value(ins.Results[0])}
		case *ssa.Jump:
			next := l.body(block.Succs[0], block)
			result.Bindings = append(result.Bindings, next.Bindings...)
			result.Result = next.Result
		}
	}
	return result
}

func (l *lowerer) value(value ssa.Value) ir.Expr {
	if c, ok := value.(*ssa.Const); ok {
		if c.Value.Kind() == constant.Bool {
			return ir.BoolLiteral(constant.BoolVal(c.Value))
		}
		return ir.IntLiteral{Value: c.Value.ExactString(), Type: l.valueType(c.Type())}
	}
	if binder, ok := l.bindings[value]; ok {
		return ir.Ref(binder)
	}
	panic("missing binding for checked SSA value: " + value.String())
}

func (l *lowerer) binary(expr *ssa.BinOp) ir.Binary {
	op, _ := subset.Binary(expr.Op)
	return ir.Binary{Op: op, Left: l.value(expr.X), Right: l.value(expr.Y), OperandType: l.valueType(expr.X.Type())}
}

func (l *lowerer) valueType(t types.Type) ir.Type {
	typ := subset.Type(t)
	l.usesWord = l.usesWord || typ.IsWord()
	return typ
}
