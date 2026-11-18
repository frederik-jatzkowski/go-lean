package subset

import (
	"go/constant"
	"go/token"
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

type AccumulatorLoop struct {
	Initial ssa.Value
	State   *ssa.Phi
	Steps   []ssa.Value
	Next    ssa.Value
}

type CountedLoop struct {
	AccumulatorLoop
	Bound ssa.Value
}

type RangeFold struct {
	AccumulatorLoop
	Source  ssa.Value
	Element *ssa.UnOp
}

type loopBlocks struct {
	entry, header, body *ssa.BasicBlock
	state               *ssa.Phi
	incoming, back      int
}

// checkCountedLoop recognizes a zero-based uint8 counter that advances by one
// while it is below an invariant uint8 bound. The increment cannot wrap because
// it is executed only when the counter is strictly below that bound.
func checkCountedLoop(fn *ssa.Function) *CountedLoop {
	blocks, ok := matchLoopBlocks(fn)
	if !ok || len(blocks.entry.Instrs) != 1 || len(blocks.header.Instrs) != 4 {
		return nil
	}
	header, body, incoming, back := blocks.header, blocks.body, blocks.incoming, blocks.back
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
	if blocks.state != state {
		return nil
	}
	last := len(body.Instrs) - 1
	step, ok := counter.Edges[back].(*ssa.BinOp)
	if !ok || step.Block() != body || step.Op != token.ADD || step.X != counter ||
		!intConstant(step.Y, 1) {
		return nil
	}
	loop := &CountedLoop{
		Bound: cond.Y, AccumulatorLoop: AccumulatorLoop{Initial: state.Edges[incoming], State: state, Next: state.Edges[back]},
	}
	available := map[ssa.Value]bool{state: true}
	steps, ok := accumulatorSteps(body.Instrs[:last], step, available)
	if !ok || !loopValue(loop.Next, available) {
		return nil
	}
	loop.Steps = steps
	return loop
}

// checkRangeFold recognizes the SSA of an index-and-value range over a slice.
// The counter starts at -1 and is incremented in the header before checking
// against the length of the same slice. A Go slice length fits in an int, so
// the counter reaches that length without overflowing.
func checkRangeFold(fn *ssa.Function) *RangeFold {
	blocks, ok := matchLoopBlocks(fn)
	if !ok || len(blocks.entry.Instrs) != 2 || len(blocks.header.Instrs) != 5 || len(blocks.body.Instrs) < 3 {
		return nil
	}
	length, ok := blocks.entry.Instrs[0].(*ssa.Call)
	if !ok || !IsLength(length) || len(length.Call.Args) != 1 {
		return nil
	}
	source := length.Call.Args[0]
	if !invariant(source, ir.SliceType(ir.Int64)) {
		return nil
	}
	header, body, incoming, back := blocks.header, blocks.body, blocks.incoming, blocks.back
	first, firstOK := header.Instrs[0].(*ssa.Phi)
	second, secondOK := header.Instrs[1].(*ssa.Phi)
	step, stepOK := header.Instrs[2].(*ssa.BinOp)
	cond, condOK := header.Instrs[3].(*ssa.BinOp)
	branch, branchOK := header.Instrs[4].(*ssa.If)
	if !firstOK || !secondOK || !stepOK || !condOK || !branchOK ||
		step.Op != token.ADD || !intConstant(step.Y, 1) ||
		cond.Op != token.LSS || cond.X != step || cond.Y != length || branch.Cond != cond {
		return nil
	}
	counter, state := first, second
	if step.X == second {
		counter, state = second, first
	}
	if step.X != counter || Type(counter.Type()) != ir.IntWord ||
		!intConstant(counter.Edges[incoming], -1) || counter.Edges[back] != step ||
		blocks.state != state || Type(state.Type()) != ir.Int64 || !invariant(state.Edges[incoming], ir.Int64) {
		return nil
	}
	addr, addrOK := body.Instrs[0].(*ssa.IndexAddr)
	elem, elemOK := body.Instrs[1].(*ssa.UnOp)
	if !addrOK || !elemOK || addr.X != source || addr.Index != step || elem.Op != token.MUL || elem.X != addr {
		return nil
	}
	available := map[ssa.Value]bool{state: true, elem: true}
	steps, ok := accumulatorSteps(body.Instrs[2:len(body.Instrs)-1], nil, available)
	next := state.Edges[back]
	if !ok || !loopValue(next, available) {
		return nil
	}
	return &RangeFold{
		Source: source, Element: elem,
		AccumulatorLoop: AccumulatorLoop{Initial: state.Edges[incoming], State: state, Steps: steps, Next: next},
	}
}

func accumulatorSteps(instructions []ssa.Instruction, skip ssa.Instruction, available map[ssa.Value]bool) ([]ssa.Value, bool) {
	var steps []ssa.Value
	for _, ins := range instructions {
		if ins == skip {
			continue
		}
		switch op := ins.(type) {
		case *ssa.BinOp:
			if Type(op.Type()) != ir.Int64 || op.Op != token.ADD && op.Op != token.SUB && op.Op != token.MUL ||
				!loopValue(op.X, available) || !loopValue(op.Y, available) {
				return nil, false
			}
			available[op] = true
			steps = append(steps, op)
		case *ssa.UnOp:
			if Type(op.Type()) != ir.Int64 || op.Op != token.SUB || !loopValue(op.X, available) {
				return nil, false
			}
			available[op] = true
			steps = append(steps, op)
		default:
			return nil, false
		}
	}
	return steps, true
}

func matchLoopBlocks(fn *ssa.Function) (loopBlocks, bool) {
	if len(fn.Blocks) != 4 || fn.Parent() != nil || fn.Signature.TypeParams().Len() != 0 ||
		Type(fn.Signature.Results().At(0).Type()) != ir.Int64 {
		return loopBlocks{}, false
	}
	entry := fn.Blocks[0]
	if len(entry.Preds) != 0 || len(entry.Succs) != 1 || !endsInJump(entry) {
		return loopBlocks{}, false
	}
	header := entry.Succs[0]
	if len(header.Preds) != 2 || len(header.Succs) != 2 {
		return loopBlocks{}, false
	}
	body, exit := header.Succs[0], header.Succs[1]
	if body == entry || body == header || exit == entry || exit == header || body == exit ||
		len(body.Preds) != 1 || body.Preds[0] != header ||
		len(exit.Preds) != 1 || exit.Preds[0] != header ||
		len(body.Succs) != 1 || body.Succs[0] != header || len(body.Instrs) < 2 || !endsInJump(body) ||
		len(exit.Succs) != 0 || len(exit.Instrs) != 1 {
		return loopBlocks{}, false
	}
	incoming, back := slices.Index(header.Preds, entry), slices.Index(header.Preds, body)
	ret, ok := exit.Instrs[0].(*ssa.Return)
	if !ok || len(ret.Results) != 1 || incoming < 0 || back < 0 {
		return loopBlocks{}, false
	}
	state, ok := ret.Results[0].(*ssa.Phi)
	return loopBlocks{entry: entry, header: header, body: body, state: state, incoming: incoming, back: back}, ok
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

func endsInJump(block *ssa.BasicBlock) bool {
	if len(block.Instrs) == 0 {
		return false
	}
	_, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Jump)
	return ok
}
