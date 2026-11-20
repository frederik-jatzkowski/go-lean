// Package structure recovers structured control-flow regions from Go SSA.
package structure

import (
	"slices"

	"golang.org/x/tools/go/ssa"
)

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
