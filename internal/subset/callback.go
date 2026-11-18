package subset

import (
	"go/token"

	"golang.org/x/tools/go/ssa"
)

func (c *checker) checkCallback(caller *ssa.Function, call *ssa.Call, value ssa.Value) error {
	fn, ok := value.(*ssa.Function)
	if !ok || len(fn.FreeVars) != 0 || (fn.Parent() != nil && fn.Parent() != caller) {
		return diagnostic(caller, call.Pos(), "slice callback must be a statically known function without captures")
	}
	if err := c.function(fn); err != nil {
		return diagnostic(caller, call.Pos(), "slice callback %s: %w", fn, err)
	}
	if !totalCallback(fn, make(map[*ssa.Function]bool)) {
		return diagnostic(caller, call.Pos(), "slice callback %s must use only total operations", fn)
	}
	return nil
}

// The ordinary checker has validated the types, call graph, and control flow.
// Restrict callbacks further so List.map cannot erase a panic or memory access.
func totalCallback(fn *ssa.Function, checked map[*ssa.Function]bool) bool {
	if checked[fn] {
		return true
	}
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			switch ins := ins.(type) {
			case *ssa.BinOp:
				if ins.Op == token.QUO {
					return false
				}
			case *ssa.UnOp:
				if ins.Op != token.SUB && ins.Op != token.NOT {
					return false
				}
			case *ssa.Call:
				if IsLength(ins) {
					continue
				}
				callee, ok := ins.Call.Value.(*ssa.Function)
				if !ok || !totalCallback(callee, checked) {
					return false
				}
			case *ssa.If, *ssa.Jump, *ssa.Phi, *ssa.Return, *ssa.Convert, *ssa.ChangeType, *ssa.Field:
			default:
				return false
			}
		}
	}
	checked[fn] = true
	return true
}
