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
	Start         ssa.Value
	Bound         ssa.Value
	Before, After []ssa.Value
	Result        ssa.Value
	Structured    *LoopState
}

type RangeFold struct {
	AccumulatorLoop
	Source     ssa.Value
	Element    *ssa.UnOp
	Structured *LoopState
}

type loopBlocks struct {
	entry, header, body, latch, exit *ssa.BasicBlock
	result                           ssa.Value
	incoming, back                   int
	backs                            []int
}

type rangeIteration struct {
	Source    ssa.Value
	Index     ssa.Value
	LatchStep *ssa.BinOp
	Element   *ssa.UnOp
	Counter   *ssa.Phi
	Length    *ssa.Call
}

// checkCountedLoop recognizes an integer counter that advances by one
// while it is below an invariant bound of the same type. The increment cannot wrap because
// it is executed only when the counter is strictly below that bound.
func checkCountedLoop(fn *ssa.Function) *CountedLoop {
	blocks, ok := matchLoopBlocks(fn)
	if !ok || len(blocks.header.Instrs) != 4 {
		return nil
	}
	header, body, incoming, back := blocks.header, blocks.body, blocks.incoming, blocks.back
	first, firstOK := header.Instrs[0].(*ssa.Phi)
	second, secondOK := header.Instrs[1].(*ssa.Phi)
	cond, condOK := header.Instrs[2].(*ssa.BinOp)
	branch, branchOK := header.Instrs[3].(*ssa.If)
	if !firstOK || !secondOK || !condOK || !branchOK || branch.Cond != cond || cond.Op != token.LSS && cond.Op != token.GTR {
		return nil
	}
	index, bound := cond.X, cond.Y
	if cond.Op == token.GTR {
		index, bound = bound, index
	}
	counter, state := first, second
	if index == second {
		counter, state = second, first
	}
	counterType := Type(counter.Type())
	start := counter.Edges[incoming]
	beforeAvailable := make(map[ssa.Value]bool)
	before, ok := invariantIntegerSteps(blocks.entry.Instrs[:len(blocks.entry.Instrs)-1], beforeAvailable)
	initial := state.Edges[incoming]
	if !ok || index != counter || !counterType.IsInteger() || !loopOperand(start, beforeAvailable, counterType) ||
		Type(state.Type()) != ir.Int64 || !loopOperand(bound, beforeAvailable, counterType) ||
		!loopOperand(initial, beforeAvailable, ir.Int64) {
		return nil
	}
	afterAvailable := map[ssa.Value]bool{state: true}
	for _, value := range before {
		afterAvailable[value] = true
	}
	after, ok := invariantIntegerSteps(blocks.exit.Instrs[:len(blocks.exit.Instrs)-1], afterAvailable)
	if !ok || !loopOperand(blocks.result, afterAvailable, Type(blocks.result.Type())) {
		return nil
	}
	last := len(body.Instrs) - 1
	step, ok := counter.Edges[back].(*ssa.BinOp)
	if !ok || step.Block() != body || step.Op != token.ADD || step.X != counter ||
		!intConstant(step.Y, 1) {
		return nil
	}
	loop := &CountedLoop{
		Start: start, Bound: bound, Before: before, After: after, Result: blocks.result,
		AccumulatorLoop: AccumulatorLoop{Initial: initial, State: state, Next: state.Edges[back]},
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
	if !ok || len(blocks.exit.Instrs) != 1 {
		return nil
	}
	iter := matchRangeIteration(blocks, 2)
	if iter == nil || Type(iter.Source.Type()) != ir.SliceType(ir.Int64) {
		return nil
	}
	for _, ins := range blocks.entry.Instrs[:len(blocks.entry.Instrs)-1] {
		if ins != iter.Length {
			return nil
		}
	}
	state, ok := blocks.result.(*ssa.Phi)
	if !ok || state == iter.Counter || state.Block() != blocks.header || Type(state.Type()) != ir.Int64 ||
		!invariant(state.Edges[blocks.incoming], ir.Int64) {
		return nil
	}
	available := map[ssa.Value]bool{state: true, iter.Element: true}
	body := blocks.body.Instrs
	steps, ok := pureInt64Steps(body[2:len(body)-1], iter.LatchStep, available)
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
	if iter := matchIndexedIteration(blocks, phiCount); iter != nil {
		return iter
	}
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
		!intConstant(counter.Edges[blocks.incoming], -1) || !allBackEdges(counter, blocks, step) {
		return nil
	}
	addr, addrOK := body[0].(*ssa.IndexAddr)
	elem, elemOK := body[1].(*ssa.UnOp)
	if !addrOK || !elemOK || addr.X != source || addr.Index != step || elem.Op != token.MUL || elem.X != addr {
		return nil
	}
	return &rangeIteration{Source: source, Index: step, Element: elem, Counter: counter, Length: length}
}

// matchIndexedIteration recognizes an ordinary zero-based for loop whose
// guard bounds indexing into the same slice. Only the unit increment is
// omitted when lowering the body to a traversal.
func matchIndexedIteration(blocks loopBlocks, phiCount int) *rangeIteration {
	header, body := blocks.header.Instrs, blocks.body.Instrs
	if len(blocks.backs) != 1 || len(header) < phiCount+2 || len(header) > phiCount+3 || len(body) < 3 || len(blocks.latch.Instrs) < 2 {
		return nil
	}
	branch, ok := header[len(header)-1].(*ssa.If)
	if !ok {
		return nil
	}
	cond, ok := branch.Cond.(*ssa.BinOp)
	if !ok || cond.Op != token.LSS || cond != header[len(header)-2] {
		return nil
	}
	counter, ok := cond.X.(*ssa.Phi)
	if !ok || counter.Block() != blocks.header || Type(counter.Type()) != ir.IntWord ||
		!intConstant(counter.Edges[blocks.incoming], 0) {
		return nil
	}
	step, ok := counter.Edges[blocks.back].(*ssa.BinOp)
	if !ok || step != blocks.latch.Instrs[len(blocks.latch.Instrs)-2] || step.Op != token.ADD || step.X != counter || !intConstant(step.Y, 1) {
		return nil
	}
	length, ok := cond.Y.(*ssa.Call)
	if !ok || !IsLength(length) || len(length.Call.Args) != 1 {
		return nil
	}
	if length.Block() == blocks.header {
		if len(header) != phiCount+3 || header[phiCount] != length {
			return nil
		}
	} else if length.Block() != blocks.entry || len(header) != phiCount+2 {
		return nil
	}
	for _, ins := range header[:phiCount] {
		if _, ok := ins.(*ssa.Phi); !ok {
			return nil
		}
	}
	source := length.Call.Args[0]
	if typ := Type(source.Type()); typ.SliceElem() == "" || !invariant(source, typ) {
		return nil
	}
	addr, addrOK := body[0].(*ssa.IndexAddr)
	elem, elemOK := body[1].(*ssa.UnOp)
	if !addrOK || !elemOK || addr.X != source || addr.Index != counter || elem.Op != token.MUL || elem.X != addr {
		return nil
	}
	return &rangeIteration{Source: source, Index: counter, LatchStep: step, Element: elem, Counter: counter, Length: length}
}

func pureInt64Steps(instructions []ssa.Instruction, skip ssa.Instruction, available map[ssa.Value]bool) ([]ssa.Value, bool) {
	var steps []ssa.Value
	for _, ins := range instructions {
		if ins == skip {
			continue
		}
		step := pureInt64Step(ins, available)
		if step == nil {
			return nil, false
		}
		available[step] = true
		steps = append(steps, step)
	}
	return steps, true
}

func pureInt64Step(ins ssa.Instruction, available map[ssa.Value]bool) ssa.Value {
	return integerStep(ins, available, ir.Int64)
}

func invariantIntegerSteps(instructions []ssa.Instruction, available map[ssa.Value]bool) ([]ssa.Value, bool) {
	var steps []ssa.Value
	for _, ins := range instructions {
		value, ok := ins.(ssa.Value)
		if !ok || !Type(value.Type()).IsInteger() || integerStep(ins, available, Type(value.Type())) == nil {
			return nil, false
		}
		steps = append(steps, value)
		available[value] = true
	}
	return steps, true
}

func loopOperand(value ssa.Value, available map[ssa.Value]bool, typ ir.Type) bool {
	return available[value] || invariant(value, typ)
}

func integerStep(ins ssa.Instruction, available map[ssa.Value]bool, typ ir.Type) ssa.Value {
	operand := func(value ssa.Value) bool {
		return available[value] || invariant(value, typ)
	}
	switch op := ins.(type) {
	case *ssa.BinOp:
		if Type(op.Type()) == typ && (op.Op == token.ADD || op.Op == token.SUB || op.Op == token.MUL) &&
			operand(op.X) && operand(op.Y) {
			return op
		}
	case *ssa.UnOp:
		if Type(op.Type()) == typ && op.Op == token.SUB && operand(op.X) {
			return op
		}
	}
	return nil
}

func matchLoopBlocks(fn *ssa.Function) (loopBlocks, bool) {
	if len(fn.Blocks) != 4 {
		return loopBlocks{}, false
	}
	blocks, ok := matchLoopRegion(fn)
	return blocks, ok && len(blocks.backs) == 1 && blocks.body == blocks.latch
}

// matchLoopRegion identifies a single-entry loop whose false guard edge exits
// directly. Every iteration path returns to the header without another cycle.
func matchLoopRegion(fn *ssa.Function) (loopBlocks, bool) {
	if len(fn.Blocks) < 4 || fn.Parent() != nil || fn.Signature.TypeParams().Len() != 0 {
		return loopBlocks{}, false
	}
	entry := fn.Blocks[0]
	if len(entry.Preds) != 0 || len(entry.Succs) != 1 || !endsInJump(entry) {
		return loopBlocks{}, false
	}
	header := entry.Succs[0]
	if len(header.Preds) < 2 || len(header.Succs) != 2 {
		return loopBlocks{}, false
	}
	body, exit := header.Succs[0], header.Succs[1]
	incoming := slices.Index(header.Preds, entry)
	if incoming < 0 || body == header || body == exit || len(body.Preds) != 1 || body.Preds[0] != header ||
		len(exit.Preds) != 1 || exit.Preds[0] != header || len(exit.Succs) != 0 || len(exit.Instrs) == 0 {
		return loopBlocks{}, false
	}
	var backs []int
	for i := range header.Preds {
		if i != incoming {
			backs = append(backs, i)
		}
	}
	back := backs[0]
	latch := header.Preds[back]
	if len(backs) == 1 && (len(latch.Succs) != 1 || latch.Succs[0] != header || !endsInJump(latch)) {
		return loopBlocks{}, false
	}
	ret, ok := exit.Instrs[len(exit.Instrs)-1].(*ssa.Return)
	if !ok || len(ret.Results) != 1 {
		return loopBlocks{}, false
	}
	seen := make(map[*ssa.BasicBlock]bool)
	active := make(map[*ssa.BasicBlock]bool)
	var visit func(*ssa.BasicBlock) bool
	visit = func(block *ssa.BasicBlock) bool {
		if block == header {
			return true
		}
		if block == entry || block == exit || active[block] || len(block.Succs) == 0 {
			return false
		}
		if seen[block] {
			return true
		}
		seen[block] = true
		active[block] = true
		for _, successor := range block.Succs {
			if !visit(successor) {
				return false
			}
		}
		delete(active, block)
		return true
	}
	if !visit(body) || len(seen)+3 != len(fn.Blocks) {
		return loopBlocks{}, false
	}
	return loopBlocks{entry: entry, header: header, body: body, latch: latch, exit: exit,
		result: ret.Results[0], incoming: incoming, back: back, backs: backs}, true
}

func allBackEdges(phi *ssa.Phi, blocks loopBlocks, want ssa.Value) bool {
	for _, edge := range blocks.backs {
		if phi.Edges[edge] != want {
			return false
		}
	}
	return true
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

// IsZero reports whether the SSA value is the integer constant zero.
func IsZero(value ssa.Value) bool { return intConstant(value, 0) }

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

// LoopState carries the header phi values through a bounded slice traversal.
type LoopState struct {
	Iteration *TraversalIteration
	Exit      *ssa.BasicBlock
	States    []*ssa.Phi
	Initial   []ssa.Value
	Next      map[*ssa.BasicBlock][]ssa.Value
}

func matchStructuredFold(fn *ssa.Function) *RangeFold {
	blocks, ok := matchLoopRegion(fn)
	if !ok {
		return nil
	}
	var phis []*ssa.Phi
	for _, ins := range blocks.header.Instrs {
		phi, ok := ins.(*ssa.Phi)
		if !ok {
			break
		}
		phis = append(phis, phi)
	}
	if len(phis) < 2 {
		return nil
	}
	iter := matchRangeIteration(blocks, len(phis))
	if iter == nil {
		return nil
	}
	for _, ins := range blocks.entry.Instrs[:len(blocks.entry.Instrs)-1] {
		if ins != iter.Length {
			return nil
		}
	}
	skip := map[ssa.Instruction]bool{iter.Element: true, iter.Element.X.(*ssa.IndexAddr): true}
	omitted := map[ssa.Value]bool{iter.Counter: true, iter.Index: true, iter.Length: true, iter.Element.X: true}
	if iter.LatchStep != nil {
		skip[iter.LatchStep] = true
		omitted[iter.LatchStep] = true
	}
	fold := &LoopState{Exit: blocks.exit, Next: make(map[*ssa.BasicBlock][]ssa.Value),
		Iteration: &TraversalIteration{Entry: blocks.body, Header: blocks.header, Skip: skip}}
	for _, phi := range phis {
		if phi == iter.Counter {
			continue
		}
		initial := phi.Edges[blocks.incoming]
		typ := Type(phi.Type())
		if !typ.IsInteger() && typ != ir.Bool || !invariant(initial, typ) {
			return nil
		}
		fold.States = append(fold.States, phi)
		fold.Initial = append(fold.Initial, initial)
		for _, edge := range blocks.backs {
			next := phi.Edges[edge]
			if !hasType(next, typ) || omitted[next] {
				return nil
			}
			pred := blocks.header.Preds[edge]
			fold.Next[pred] = append(fold.Next[pred], next)
		}
	}
	for _, block := range fn.Blocks {
		if block == blocks.entry || block == blocks.header {
			continue
		}
		for _, ins := range block.Instrs {
			if skip[ins] {
				continue
			}
			if _, ok := ins.(*ssa.Return); !ok && !iterationInstruction(ins) {
				return nil
			}
			for _, operand := range ins.Operands(nil) {
				if operand != nil && (omitted[*operand] || block == blocks.exit && *operand == iter.Element) {
					return nil
				}
			}
		}
	}
	return &RangeFold{Source: iter.Source, Element: iter.Element, Structured: fold}
}

func (c *checker) checkLoopState(fn *ssa.Function, spec *LoopState) error {
	if err := c.checkIteration(fn, spec.Iteration); err != nil {
		return err
	}
	for _, ins := range spec.Exit.Instrs {
		if _, ok := ins.(*ssa.Return); !ok && !iterationInstruction(ins) {
			return diagnostic(fn, ins.Pos(), "unsupported loop continuation instruction: %s", ins)
		}
		if err := c.instruction(fn, ins); err != nil {
			return err
		}
	}
	return nil
}

func matchStructuredCountedLoop(fn *ssa.Function) *CountedLoop {
	blocks, ok := matchLoopRegion(fn)
	if !ok {
		return nil
	}
	header := blocks.header.Instrs
	if len(header) < 3 {
		return nil
	}
	cond, condOK := header[len(header)-2].(*ssa.BinOp)
	branch, branchOK := header[len(header)-1].(*ssa.If)
	if !condOK || !branchOK || branch.Cond != cond || cond.Op != token.LSS && cond.Op != token.GTR {
		return nil
	}
	index, bound := cond.X, cond.Y
	if cond.Op == token.GTR {
		index, bound = bound, index
	}
	counter, ok := index.(*ssa.Phi)
	if !ok || counter.Block() != blocks.header || !Type(counter.Type()).IsInteger() {
		return nil
	}
	available := make(map[ssa.Value]bool)
	before, ok := invariantIntegerSteps(blocks.entry.Instrs[:len(blocks.entry.Instrs)-1], available)
	start := counter.Edges[blocks.incoming]
	if !ok || !loopOperand(start, available, Type(counter.Type())) || !loopOperand(bound, available, Type(counter.Type())) {
		return nil
	}
	for _, edge := range blocks.backs {
		step, ok := counter.Edges[edge].(*ssa.BinOp)
		if !ok || step.Op != token.ADD || step.X != counter || !intConstant(step.Y, 1) {
			return nil
		}
	}
	spec := &LoopState{Exit: blocks.exit, Next: make(map[*ssa.BasicBlock][]ssa.Value),
		Iteration: &TraversalIteration{Entry: blocks.body, Header: blocks.header}}
	for _, ins := range header[:len(header)-2] {
		phi, ok := ins.(*ssa.Phi)
		if !ok {
			return nil
		}
		typ := Type(phi.Type())
		initial := phi.Edges[blocks.incoming]
		if !typ.IsInteger() && typ != ir.Bool || !loopOperand(initial, available, typ) {
			return nil
		}
		spec.States = append(spec.States, phi)
		spec.Initial = append(spec.Initial, initial)
		for _, edge := range blocks.backs {
			next := phi.Edges[edge]
			if !hasType(next, typ) {
				return nil
			}
			pred := blocks.header.Preds[edge]
			spec.Next[pred] = append(spec.Next[pred], next)
		}
	}
	for _, block := range fn.Blocks {
		if block == blocks.entry || block == blocks.header || block == blocks.exit {
			continue
		}
		for _, ins := range block.Instrs {
			switch ins := ins.(type) {
			case *ssa.Call:
				return nil
			case *ssa.UnOp:
				if ins.Op == token.MUL {
					return nil
				}
			case *ssa.BinOp:
				if op, _ := Binary(ins.Op); op.PanicsOnZeroDivisor() {
					return nil
				}
			default:
				if !iterationInstruction(ins) {
					return nil
				}
			}
		}
	}
	return &CountedLoop{Start: start, Bound: bound, Before: before, Structured: spec}
}
