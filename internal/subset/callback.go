package subset

import (
	"go/token"

	"golang.org/x/tools/go/ssa"
)

func (c *checker) checkCallback(caller *ssa.Function, call *ssa.Call, value ssa.Value, build *SliceBuild) error {
	fn, ok := value.(*ssa.Function)
	if closure, isClosure := value.(*ssa.MakeClosure); isClosure {
		fn, ok = closure.Fn.(*ssa.Function)
	}
	if !ok || fn.Parent() != nil && fn.Parent() != caller {
		return diagnostic(caller, call.Pos(), "slice callback must be a statically known function")
	}
	if err := c.function(fn); err != nil {
		return diagnostic(caller, call.Pos(), "slice callback %s: %w", fn, err)
	}
	build.Callbacks = append(build.Callbacks, fn)
	return nil
}

// callbackMayPanic conservatively selects the monadic traversal. Lowering
// independently knows which concrete callbacks need to be lifted to Option.
func callbackMayPanic(fn *ssa.Function, known map[*ssa.Function]bool) bool {
	if effect, ok := known[fn]; ok {
		return effect
	}
	known[fn] = true
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			switch ins := ins.(type) {
			case *ssa.BinOp:
				if op, _ := Binary(ins.Op); op.PanicsOnZeroDivisor() {
					known[fn] = true
					return true
				}
			case *ssa.UnOp:
				if ins.Op != token.SUB && ins.Op != token.NOT {
					known[fn] = true
					return true
				}
			case *ssa.Call:
				if !IsLength(ins) {
					callee := ins.Call.StaticCallee()
					if callee == nil || callbackMayPanic(callee, known) {
						known[fn] = true
						return true
					}
				}
			case *ssa.If, *ssa.Jump, *ssa.Phi, *ssa.Return, *ssa.Convert, *ssa.ChangeType, *ssa.Field:
			default:
				known[fn] = true
				return true
			}
		}
	}
	known[fn] = false
	return false
}
