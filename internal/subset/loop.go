package subset

import (
	"go/constant"
	"go/token"
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

type CountedLoop struct {
	Bound   ssa.Value
	Initial ssa.Value
	State   *ssa.Phi
	Steps   []ssa.Value
	Next    ssa.Value
}

// checkCountedLoop recognizes a zero-based uint8 counter that advances by one
// while it is below an invariant uint8 bound. The increment cannot wrap because
// it is executed only when the counter is strictly below that bound.
func checkCountedLoop(fn *ssa.Function) *CountedLoop {
	if len(fn.Blocks) != 4 || fn.Parent() != nil || fn.Signature.TypeParams().Len() != 0 ||
		Type(fn.Signature.Results().At(0).Type()) != ir.Int64 {
		return nil
	}
	entry := fn.Blocks[0]
	if !jumpOnly(entry) {
		return nil
	}
	header := entry.Succs[0]
	if len(header.Preds) != 2 || len(header.Succs) != 2 || len(header.Instrs) != 4 {
		return nil
	}
	body, exit := header.Succs[0], header.Succs[1]
	if body == entry || body == header || exit == entry || exit == header || body == exit ||
		len(body.Preds) != 1 || body.Preds[0] != header ||
		len(exit.Preds) != 1 || exit.Preds[0] != header ||
		len(body.Succs) != 1 || body.Succs[0] != header || len(body.Instrs) < 2 ||
		len(exit.Succs) != 0 || len(exit.Instrs) != 1 {
		return nil
	}
	incoming, back := slices.Index(header.Preds, entry), slices.Index(header.Preds, body)
	if incoming < 0 || back < 0 {
		return nil
	}
	first, firstOK := header.Instrs[0].(*ssa.Phi)
	second, secondOK := header.Instrs[1].(*ssa.Phi)
	cond, condOK := header.Instrs[2].(*ssa.BinOp)
	branch, branchOK := header.Instrs[3].(*ssa.If)
	if !firstOK || !secondOK || !condOK || !branchOK || branch.Cond != cond || cond.Op != token.LSS {
		return nil
	}
	counter, state := first, second
	if cond.X == second {
		counter, state = second, first
	}
	if cond.X != counter || Type(counter.Type()) != ir.UInt8 || !intConstant(counter.Edges[incoming], 0) ||
		Type(state.Type()) != ir.Int64 || !invariant(cond.Y, ir.UInt8) ||
		!invariant(state.Edges[incoming], ir.Int64) {
		return nil
	}
	ret, ok := exit.Instrs[0].(*ssa.Return)
	if !ok || len(ret.Results) != 1 || ret.Results[0] != state {
		return nil
	}
	last := len(body.Instrs) - 1
	step, ok := counter.Edges[back].(*ssa.BinOp)
	if !ok || step.Block() != body || step.Op != token.ADD || step.X != counter ||
		!intConstant(step.Y, 1) {
		return nil
	}
	if _, ok := body.Instrs[last].(*ssa.Jump); !ok {
		return nil
	}
	loop := &CountedLoop{Bound: cond.Y, Initial: state.Edges[incoming], State: state, Next: state.Edges[back]}
	available := map[ssa.Value]bool{state: true}
	for _, ins := range body.Instrs[:last] {
		if ins == step {
			continue
		}
		switch op := ins.(type) {
		case *ssa.BinOp:
			if Type(op.Type()) != ir.Int64 || op.Op != token.ADD && op.Op != token.SUB && op.Op != token.MUL ||
				!loopValue(op.X, available) || !loopValue(op.Y, available) {
				return nil
			}
			available[op] = true
			loop.Steps = append(loop.Steps, op)
		case *ssa.UnOp:
			if Type(op.Type()) != ir.Int64 || op.Op != token.SUB || !loopValue(op.X, available) {
				return nil
			}
			available[op] = true
			loop.Steps = append(loop.Steps, op)
		default:
			return nil
		}
	}
	if !loopValue(loop.Next, available) {
		return nil
	}
	return loop
}

func loopValue(value ssa.Value, available map[ssa.Value]bool) bool {
	return available[value] || invariant(value, ir.Int64)
}

func invariant(value ssa.Value, typ ir.Type) bool {
	switch value.(type) {
	case *ssa.Parameter, *ssa.Const:
		return hasType(value, typ)
	default:
		return false
	}
}

func intConstant(value ssa.Value, want int64) bool {
	c, ok := value.(*ssa.Const)
	if !ok || c.Value == nil || c.Value.Kind() != constant.Int {
		return false
	}
	n, exact := constant.Int64Val(c.Value)
	return exact && n == want
}

func jumpOnly(block *ssa.BasicBlock) bool {
	if len(block.Preds) != 0 || len(block.Succs) != 1 || len(block.Instrs) != 1 {
		return false
	}
	_, ok := block.Instrs[0].(*ssa.Jump)
	return ok
}
