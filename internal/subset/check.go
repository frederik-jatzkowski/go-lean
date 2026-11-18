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
		sig.Results().Len() != 1 || Type(sig.Results().At(0).Type()) == "" {
		return diagnostic(fn, fn.Pos(), "expected a top-level function with one supported scalar result and no type parameters or variadic arguments")
	}
	for _, param := range fn.Params {
		if Type(param.Type()) == "" {
			return diagnostic(fn, param.Pos(), "parameter must have a supported scalar type")
		}
	}
	c.visiting[fn] = true
	if err := checkAcyclic(fn); err != nil {
		return err
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

func checkAcyclic(fn *ssa.Function) error {
	const visiting, done = 1, 2
	states := make([]int, len(fn.Blocks))
	var visit func(*ssa.BasicBlock) error
	visit = func(block *ssa.BasicBlock) error {
		switch states[block.Index] {
		case visiting:
			return diagnostic(fn, block.Instrs[0].Pos(), "control-flow loops are unsupported")
		case done:
			return nil
		}
		states[block.Index] = visiting
		for _, successor := range block.Succs {
			if err := visit(successor); err != nil {
				return err
			}
		}
		states[block.Index] = done
		return nil
	}
	return visit(fn.Blocks[0])
}

func (c *checker) instruction(fn *ssa.Function, ins ssa.Instruction) error {
	switch ins := ins.(type) {
	case *ssa.BinOp:
		_, supported := Binary(ins.Op)
		typ := Type(ins.X.Type())
		if supported && scalar(ins.X) && hasType(ins.Y, typ) &&
			(typ.IsInteger() || ins.Op == token.EQL || ins.Op == token.NEQ) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "unsupported runtime operation %s on %s and %s", ins.Op, ins.X.Type(), ins.Y.Type())
	case *ssa.UnOp:
		if ins.Op == token.SUB && Type(ins.X.Type()).IsInteger() && scalar(ins.X) ||
			ins.Op == token.NOT && hasType(ins.X, ir.Bool) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "unsupported unary operation %s on %s", ins.Op, ins.X.Type())
	case *ssa.Convert:
		from, to := Type(ins.X.Type()), Type(ins.Type())
		if from.IsWord() && to.IsWord() && scalar(ins.X) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "unsupported conversion from %s to %s", ins.X.Type(), ins.Type())
	case *ssa.Call:
		callee := ins.Call.StaticCallee()
		if callee == nil {
			return diagnostic(fn, ins.Pos(), "unsupported call to %s; expected a statically resolved Go function", ins.Call.Value)
		}
		for _, arg := range ins.Call.Args {
			if !scalar(arg) {
				return diagnostic(fn, ins.Pos(), "call to %s requires supported scalar arguments", callee)
			}
		}
		if err := c.function(callee); err != nil {
			return diagnostic(fn, ins.Pos(), "call to %s: %w", callee, err)
		}
		return nil
	case *ssa.If:
		if hasType(ins.Cond, ir.Bool) {
			return nil
		}
		return diagnostic(fn, ins.Cond.Pos(), "branch condition must be a supported bool value")
	case *ssa.Phi:
		if Type(ins.Type()) != ir.Bool {
			return diagnostic(fn, ins.Pos(), "control-flow joins with non-bool values are unsupported")
		}
		for _, edge := range ins.Edges {
			if !hasType(edge, ir.Bool) {
				return diagnostic(fn, ins.Pos(), "control-flow joins require supported bool values")
			}
		}
		return nil
	case *ssa.Return:
		if len(ins.Results) == 1 && scalar(ins.Results[0]) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "return must have one supported scalar value")
	case *ssa.Jump:
		return nil
	default:
		return diagnostic(fn, ins.Pos(), "unsupported SSA instruction %T", ins)
	}
}

func hasType(value ssa.Value, want ir.Type) bool {
	return Type(value.Type()) == want && scalar(value)
}

func scalar(value ssa.Value) bool {
	typ := Type(value.Type())
	if typ == "" {
		return false
	}
	switch value := value.(type) {
	case *ssa.Const:
		return value.Value != nil &&
			(typ.IsInteger() && value.Value.Kind() == constant.Int ||
				typ == ir.Bool && value.Value.Kind() == constant.Bool)
	case *ssa.Parameter, *ssa.BinOp, *ssa.UnOp, *ssa.Call, *ssa.Phi, *ssa.Convert:
		return true
	default:
		return false
	}
}

func Type(t types.Type) ir.Type {
	if basic, ok := types.Unalias(t).(*types.Basic); ok {
		switch basic.Kind() {
		case types.Int:
			return ir.IntWord
		case types.Uint:
			return ir.UIntWord
		case types.Int8:
			return ir.Int8
		case types.Int16:
			return ir.Int16
		case types.Int32:
			return ir.Int32
		case types.Int64:
			return ir.Int64
		case types.Uint8:
			return ir.UInt8
		case types.Uint16:
			return ir.UInt16
		case types.Uint32:
			return ir.UInt32
		case types.Uint64:
			return ir.UInt64
		case types.Bool, types.UntypedBool:
			return ir.Bool
		}
	}
	return ""
}

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
