// Package structure recovers structured control-flow regions from Go SSA.
package structure

import (
	"go/ast"
	"slices"

	"golang.org/x/tools/go/ssa"
)

// SecondSourceLoop returns the second loop in the function's own source body.
func SecondSourceLoop(fn *ssa.Function) ast.Stmt {
	syntax := fn.Syntax()
	if syntax == nil {
		return nil
	}
	var second ast.Stmt
	sawLoop := false
	ast.Inspect(syntax, func(node ast.Node) bool {
		_, literal := node.(*ast.FuncLit)
		if second != nil || literal && node != syntax {
			return false
		}
		switch node.(type) {
		case *ast.ForStmt, *ast.RangeStmt:
			if sawLoop {
				second = node.(ast.Stmt)
			}
			sawLoop = true
		}
		return true
	})
	return second
}

// SingleLoop finds one loop header and confirms that removing its back edges
// leaves an acyclic graph, including the prelude and all exit paths.
func SingleLoop(fn *ssa.Function) (header *ssa.BasicBlock, backs []int) {
	for _, block := range fn.Blocks {
		for _, succ := range block.Succs {
			if !succ.Dominates(block) {
				continue
			}
			if header != nil && header != succ {
				return nil, nil
			}
			header = succ
		}
	}
	if header == nil || header == fn.Blocks[0] {
		return nil, nil
	}
	for i, pred := range header.Preds {
		if header.Dominates(pred) {
			backs = append(backs, i)
		}
	}
	state := make(map[*ssa.BasicBlock]uint8)
	var acyclic func(*ssa.BasicBlock) bool
	acyclic = func(block *ssa.BasicBlock) bool {
		switch state[block] {
		case 1:
			return false
		case 2:
			return true
		}
		state[block] = 1
		for _, succ := range block.Succs {
			if succ == header && header.Dominates(block) {
				continue
			}
			if !acyclic(succ) {
				return false
			}
		}
		state[block] = 2
		return true
	}
	if !acyclic(fn.Blocks[0]) {
		return nil, nil
	}
	if len(header.Succs) == 2 {
		seen := make(map[*ssa.BasicBlock]bool)
		var reachesHeader func(*ssa.BasicBlock) bool
		reachesHeader = func(block *ssa.BasicBlock) bool {
			if block == header {
				return true
			}
			if seen[block] {
				return false
			}
			seen[block] = true
			for _, succ := range block.Succs {
				if reachesHeader(succ) {
					return true
				}
			}
			return false
		}
		if reachesHeader(header.Succs[1]) {
			return nil, nil
		}
	}
	return header, backs
}

// LoopRegion describes the control-flow edges of a single-entry loop.
type LoopRegion struct {
	Entry, Header, Body, Latch, Exit *ssa.BasicBlock
	Result                           ssa.Value
	Incoming, Back                   int
	Backs                            []int
}

// MatchLoopRegion identifies a single-entry loop whose false guard edge exits
// directly. Every iteration path returns to the header without another cycle.
func MatchLoopRegion(fn *ssa.Function) (LoopRegion, bool) {
	if len(fn.Blocks) < 4 || fn.Parent() != nil || fn.Signature.TypeParams().Len() != 0 {
		return LoopRegion{}, false
	}
	entry := fn.Blocks[0]
	if len(entry.Preds) != 0 || len(entry.Succs) != 1 || !EndsInJump(entry) {
		return LoopRegion{}, false
	}
	header := entry.Succs[0]
	if len(header.Preds) < 2 || len(header.Succs) != 2 {
		return LoopRegion{}, false
	}
	body, exit := header.Succs[0], header.Succs[1]
	incoming := slices.Index(header.Preds, entry)
	if incoming < 0 || body == header || body == exit || len(body.Preds) != 1 || body.Preds[0] != header ||
		len(exit.Preds) != 1 || exit.Preds[0] != header || len(exit.Succs) != 0 || len(exit.Instrs) == 0 {
		return LoopRegion{}, false
	}
	var backs []int
	for i := range header.Preds {
		if i != incoming {
			backs = append(backs, i)
		}
	}
	back := backs[0]
	latch := header.Preds[back]
	if len(backs) == 1 && (len(latch.Succs) != 1 || latch.Succs[0] != header || !EndsInJump(latch)) {
		return LoopRegion{}, false
	}
	ret, ok := exit.Instrs[len(exit.Instrs)-1].(*ssa.Return)
	if !ok || len(ret.Results) == 0 {
		return LoopRegion{}, false
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
		return LoopRegion{}, false
	}
	blocks := LoopRegion{Entry: entry, Header: header, Body: body, Latch: latch, Exit: exit,
		Incoming: incoming, Back: back, Backs: backs}
	if len(ret.Results) == 1 {
		blocks.Result = ret.Results[0]
	}
	return blocks, true
}

// EndsInJump reports whether block ends with an unconditional jump.
func EndsInJump(block *ssa.BasicBlock) bool {
	if len(block.Instrs) == 0 {
		return false
	}
	_, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Jump)
	return ok
}
