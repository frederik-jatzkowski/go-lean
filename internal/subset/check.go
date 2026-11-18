// Package subset checks the reachable SSA that the Lean backend can represent.
package subset

import (
	"fmt"
	"go/constant"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

// Checked holds the validated functions in dependency-first order.
type Checked struct {
	root      *ssa.Package
	functions []*ssa.Function
}

func (c Checked) Root() *ssa.Package         { return c.root }
func (c Checked) Functions() []*ssa.Function { return c.functions }

func Check(program gosource.Program) (Checked, error) {
	c := checker{
		visiting: make(map[*ssa.Function]bool),
		done:     make(map[*ssa.Function]bool),
	}
	for _, fn := range program.Roots {
		if err := c.function(fn); err != nil {
			return Checked{}, err
		}
	}
	return Checked{root: program.Package, functions: c.ordered}, nil
}

type checker struct {
	visiting map[*ssa.Function]bool
	done     map[*ssa.Function]bool
	ordered  []*ssa.Function
}

func (c *checker) function(fn *ssa.Function) error {
	if c.done[fn] {
		return nil
	}
	if c.visiting[fn] {
		return diagnostic(fn, fn.Pos(), "recursive calls are unsupported")
	}
	if len(fn.Blocks) == 0 {
		return diagnostic(fn, fn.Pos(), "Go body unavailable for %s", fn)
	}
	sig := fn.Signature
	if fn.Pkg == nil || fn.Parent() != nil || fn.Synthetic != "" || sig.Recv() != nil ||
		sig.TypeParams().Len() != 0 || sig.Variadic() ||
		sig.Results().Len() != 1 || !isInt64(sig.Results().At(0).Type()) {
		return diagnostic(fn, fn.Pos(), "expected a top-level function with an int64 result and no type parameters or variadic arguments")
	}
	for _, param := range fn.Params {
		if !isInt64(param.Type()) {
			return diagnostic(fn, param.Pos(), "parameter must have type int64")
		}
	}
	c.visiting[fn] = true
	for i, block := range fn.Blocks {
		if (i == 0 && len(block.Preds) != 0) || (i != 0 && len(block.Preds) != 1) {
			return diagnostic(fn, block.Instrs[0].Pos(), "control flow that joins or loops is unsupported")
		}
	}
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			if err := c.instruction(fn, ins); err != nil {
				return err
			}
		}
	}
	delete(c.visiting, fn)
	c.done[fn] = true
	c.ordered = append(c.ordered, fn)
	return nil
}

func (c *checker) instruction(fn *ssa.Function, ins ssa.Instruction) error {
	switch ins := ins.(type) {
	case *ssa.BinOp:
		_, supported := Binary(ins.Op)
		if supported && integer(ins.X) && integer(ins.Y) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "unsupported runtime operation %s on %s and %s", ins.Op, ins.X.Type(), ins.Y.Type())
	case *ssa.UnOp:
		if ins.Op == token.SUB && integer(ins.X) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "unsupported unary operation %s on %s", ins.Op, ins.X.Type())
	case *ssa.Call:
		callee := ins.Call.StaticCallee()
		if callee == nil {
			return diagnostic(fn, ins.Pos(), "unsupported call to %s; expected a statically resolved Go function", ins.Call.Value)
		}
		for _, arg := range ins.Call.Args {
			if !integer(arg) {
				return diagnostic(fn, ins.Pos(), "call to %s must have int64 arguments", callee)
			}
		}
		if err := c.function(callee); err != nil {
			return diagnostic(fn, ins.Pos(), "call to %s: %w", callee, err)
		}
		return nil
	case *ssa.If:
		switch cond := ins.Cond.(type) {
		case *ssa.Const:
			if cond.Value != nil && cond.Value.Kind() == constant.Bool {
				return nil
			}
		case *ssa.BinOp:
			if IsComparison(cond.Op) && integer(cond.X) && integer(cond.Y) {
				return nil
			}
		}
		return diagnostic(fn, ins.Cond.Pos(), "branch must compare integers")
	case *ssa.Return:
		if len(ins.Results) == 1 && integer(ins.Results[0]) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "return must have one int64 value")
	case *ssa.Jump:
		return nil
	default:
		return diagnostic(fn, ins.Pos(), "unsupported SSA instruction %T", ins)
	}
}

func integer(value ssa.Value) bool {
	if !isInt64(value.Type()) {
		return false
	}
	switch value := value.(type) {
	case *ssa.Const:
		return value.Value != nil && value.Value.Kind() == constant.Int
	case *ssa.Parameter, *ssa.BinOp, *ssa.UnOp, *ssa.Call:
		return true
	default:
		return false
	}
}

func isInt64(t types.Type) bool { return types.Identical(t, types.Typ[types.Int64]) }

func diagnostic(fn *ssa.Function, pos token.Pos, format string, args ...any) error {
	if !pos.IsValid() {
		pos = fn.Pos()
	}
	return fmt.Errorf("%s: %w", fn.Prog.Fset.Position(pos), fmt.Errorf(format, args...))
}

var binary = map[token.Token]ir.Operator{
	token.ADD: ir.Add, token.SUB: ir.Subtract, token.MUL: ir.Multiply,
	token.QUO: ir.Divide,
	token.EQL: ir.Equal, token.NEQ: ir.NotEqual, token.LSS: ir.Less,
	token.LEQ: ir.LessEqual, token.GTR: ir.Greater, token.GEQ: ir.GreaterEqual,
}

func Binary(op token.Token) (ir.Operator, bool) {
	result, ok := binary[op]
	return result, ok
}

func IsComparison(op token.Token) bool {
	mapped, ok := Binary(op)
	return ok && mapped >= ir.Equal
}
