package subset

import (
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/structure"
	"golang.org/x/tools/go/ssa"
)

// matchAppendFold validates the preheader and checks ownership of the optional
// slice accumulator. The ordinary fold path still accepts just the range length.
func matchAppendFold(fn *ssa.Function, blocks structure.LoopRegion, iter *rangeIteration,
	phis []*ssa.Phi, skip map[ssa.Instruction]bool) (*ssa.MakeSlice, map[*ssa.Call]ssa.Value, bool) {
	var dst *ssa.MakeSlice
	for _, ins := range blocks.Entry.Instrs[:len(blocks.Entry.Instrs)-1] {
		if ins == iter.Length {
			continue
		}
		switch ins := ins.(type) {
		case *ssa.Call:
			if !lengthOf(ins, iter.Source) {
				return nil, nil, false
			}
		case *ssa.MakeSlice:
			elem := Type(ins.Type()).SliceElem()
			if dst != nil || !IsZero(ins.Len) || !lengthOf(ins.Cap, iter.Source) ||
				!(elem.IsInteger() || elem == ir.Bool || elem == ir.Bytes || elem == ir.Float32 || elem == ir.Float64) {
				return nil, nil, false
			}
			dst = ins
		default:
			return nil, nil, false
		}
	}
	if dst == nil {
		for _, ins := range blocks.Entry.Instrs[:len(blocks.Entry.Instrs)-1] {
			if ins != iter.Length {
				return nil, nil, false
			}
		}
		return nil, nil, true
	}
	for _, ins := range blocks.Entry.Instrs[:len(blocks.Entry.Instrs)-1] {
		if ins != iter.Length && ins != dst && ins != dst.Cap.(*ssa.Call) {
			return nil, nil, false
		}
	}
	var output *ssa.Phi
	for _, phi := range phis {
		if phi.Edges[blocks.Incoming] == dst {
			if output != nil {
				return nil, nil, false
			}
			output = phi
		}
	}
	if output == nil || len(blocks.Exit.Instrs) != 1 {
		return nil, nil, false
	}
	ret := blocks.Exit.Instrs[0].(*ssa.Return)
	if slices.Index(ret.Results, ssa.Value(output)) < 0 {
		return nil, nil, false
	}
	for _, result := range ret.Results {
		if Type(result.Type()).SliceElem() != "" && result != output {
			return nil, nil, false
		}
		if key, _ := Type(result.Type()).MapShape(); key != "" {
			return nil, nil, false
		}
	}
	if len(*dst.Referrers()) != 1 || (*dst.Referrers())[0] != output {
		return nil, nil, false
	}
	appends := make(map[*ssa.Call]ssa.Value)
	merges := make(map[*ssa.Phi]bool)
	for _, block := range fn.Blocks {
		if block == blocks.Entry || block == blocks.Header || block == blocks.Exit {
			continue
		}
		for index, ins := range block.Instrs {
			if phi, ok := ins.(*ssa.Phi); ok && Type(phi.Type()).SliceElem() != "" {
				if Type(phi.Type()) != Type(output.Type()) {
					return nil, nil, false
				}
				merges[phi] = true
			}
			call, ok := ins.(*ssa.Call)
			if !ok || !builtinNamed(call, "append") {
				continue
			}
			element, packaging := singleAppendArgument(call, index)
			if element == nil || call.Call.Args[0] != output {
				return nil, nil, false
			}
			for _, temp := range packaging {
				skip[temp] = true
			}
			appends[call] = element
		}
	}
	if len(appends) == 0 || !validateAppendPaths(blocks, output, appends, merges) {
		return nil, nil, false
	}
	return dst, appends, true
}

func validateAppendPaths(blocks structure.LoopRegion, output *ssa.Phi, appends map[*ssa.Call]ssa.Value, merges map[*ssa.Phi]bool) bool {
	type path struct {
		block, pred *ssa.BasicBlock
		current     ssa.Value
		appended    bool
	}
	seen := make(map[path]bool)
	var visit func(path) bool
	visit = func(p path) bool {
		edge := slices.Index(p.block.Preds, p.pred)
		if p.block == blocks.Header {
			return output.Edges[edge] == p.current
		}
		if seen[p] {
			return true
		}
		seen[p] = true
		for _, ins := range p.block.Instrs {
			switch ins := ins.(type) {
			case *ssa.Phi:
				if merges[ins] {
					if ins.Edges[edge] != p.current {
						return false
					}
					p.current = ins
				}
			case *ssa.Call:
				if appends[ins] != nil {
					if p.appended || p.current != output {
						return false
					}
					p.current, p.appended = ins, true
				}
			}
		}
		for _, successor := range p.block.Succs {
			if !visit(path{successor, p.block, p.current, p.appended}) {
				return false
			}
		}
		return true
	}
	return visit(path{blocks.Body, blocks.Header, output, false})
}

func builtinNamed(call *ssa.Call, name string) bool {
	builtin, ok := call.Call.Value.(*ssa.Builtin)
	return ok && builtin.Name() == name
}

// singleAppendArgument recognizes the compiler-owned variadic argument buffer.
func singleAppendArgument(call *ssa.Call, index int) (ssa.Value, []ssa.Instruction) {
	if !builtinNamed(call, "append") || index < 4 || len(call.Call.Args) != 2 {
		return nil, nil
	}
	steps := call.Block().Instrs[index-4 : index+1]
	store, ok := steps[2].(*ssa.Store)
	if !ok || !supportedValue(store.Val) || matchSingleAppend(steps, call.Call.Args[0], store.Val) != call {
		return nil, nil
	}
	for i, want := range []int{2, 1, 0, 1} {
		if value, ok := steps[i].(ssa.Value); ok && len(*value.Referrers()) != want {
			return nil, nil
		}
	}
	return store.Val, steps[:4]
}

func (c *checker) checkAppendFold(fn *ssa.Function, fold *RangeFold) error {
	spec := fold.Structured
	for _, block := range fn.Blocks {
		if block == fn.Blocks[0] || block == spec.Iteration.Header {
			continue
		}
		for _, ins := range block.Instrs {
			if spec.Iteration.Skip[ins] {
				continue
			}
			if call, ok := ins.(*ssa.Call); ok && fold.Appends[call] != nil {
				continue
			}
			if err := c.instruction(fn, ins); err != nil {
				return err
			}
		}
	}
	return nil
}
