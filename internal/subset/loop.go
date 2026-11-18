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
	result              ssa.Value
	incoming, back      int
}

type rangeIteration struct {
	Source  ssa.Value
	Index   *ssa.BinOp
	Element *ssa.UnOp
	Counter *ssa.Phi
	Length  *ssa.Call
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
	if blocks.result != state {
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
	steps, ok := pureInt64Steps(body.Instrs[:last], step, available)
	if !ok || !loopValue(loop.Next, available) {
		return nil
	}
	loop.Steps = steps
	return loop
}

func checkRangeFold(fn *ssa.Function) *RangeFold {
	blocks, ok := matchLoopBlocks(fn)
	if !ok || len(blocks.entry.Instrs) != 2 {
		return nil
	}
	iter := matchRangeIteration(blocks, 2)
	if iter == nil || iter.Length != blocks.entry.Instrs[0] || Type(iter.Source.Type()) != ir.SliceType(ir.Int64) {
		return nil
	}
	state, ok := blocks.result.(*ssa.Phi)
	if !ok || state == iter.Counter || state.Block() != blocks.header || Type(state.Type()) != ir.Int64 ||
		!invariant(state.Edges[blocks.incoming], ir.Int64) {
		return nil
	}
	available := map[ssa.Value]bool{state: true, iter.Element: true}
	body := blocks.body.Instrs
	steps, ok := pureInt64Steps(body[2:len(body)-1], nil, available)
	next := state.Edges[blocks.back]
	if !ok || !loopValue(next, available) {
		return nil
	}
	return &RangeFold{
		Source: iter.Source, Element: iter.Element,
		AccumulatorLoop: AccumulatorLoop{Initial: state.Edges[blocks.incoming], State: state, Steps: steps, Next: next},
	}
}

// matchRangeIteration verifies that the counter starts at -1, advances once
// per iteration, and indexes the same slice whose length bounds the loop.
// A Go slice's length fits in an int, so the counter cannot wrap.
func matchRangeIteration(blocks loopBlocks, phiCount int) *rangeIteration {
	header, body := blocks.header.Instrs, blocks.body.Instrs
	if len(header) != phiCount+3 || len(body) < 3 {
		return nil
	}
	for _, ins := range header[:phiCount] {
		if _, ok := ins.(*ssa.Phi); !ok {
			return nil
		}
	}
	step, stepOK := header[phiCount].(*ssa.BinOp)
	cond, condOK := header[phiCount+1].(*ssa.BinOp)
	branch, branchOK := header[phiCount+2].(*ssa.If)
	if !stepOK || !condOK || !branchOK || step.Op != token.ADD || !intConstant(step.Y, 1) ||
		cond.Op != token.LSS || cond.X != step || branch.Cond != cond {
		return nil
	}
	length, ok := cond.Y.(*ssa.Call)
	if !ok || length.Block() != blocks.entry || !IsLength(length) || len(length.Call.Args) != 1 {
		return nil
	}
	source := length.Call.Args[0]
	typ := Type(source.Type())
	if typ.SliceElem() == "" || !invariant(source, typ) {
		return nil
	}
	counter, ok := step.X.(*ssa.Phi)
	if !ok || counter.Block() != blocks.header || Type(counter.Type()) != ir.IntWord ||
		!intConstant(counter.Edges[blocks.incoming], -1) || counter.Edges[blocks.back] != step {
		return nil
	}
	addr, addrOK := body[0].(*ssa.IndexAddr)
	elem, elemOK := body[1].(*ssa.UnOp)
	if !addrOK || !elemOK || addr.X != source || addr.Index != step || elem.Op != token.MUL || elem.X != addr {
		return nil
	}
	return &rangeIteration{Source: source, Index: step, Element: elem, Counter: counter, Length: length}
}

func pureInt64Steps(instructions []ssa.Instruction, skip ssa.Instruction, available map[ssa.Value]bool) ([]ssa.Value, bool) {
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
	if len(fn.Blocks) != 4 || fn.Parent() != nil || fn.Signature.TypeParams().Len() != 0 {
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
	return loopBlocks{entry: entry, header: header, body: body, result: ret.Results[0], incoming: incoming, back: back}, true
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
