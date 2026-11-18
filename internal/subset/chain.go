package subset

import (
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

// ChainRecursion records a nil-guarded traversal of a finite acyclic chain.
// Only the validated self-call may observe the next node pointer.
type ChainRecursion struct {
	Input  *ssa.Parameter
	Head   *ssa.UnOp
	Tail   *ssa.UnOp
	Base   ssa.Value
	Steps  []ssa.Value
	Result ssa.Value
}

func checkChainRecursion(fn *ssa.Function) *ChainRecursion {
	if fn.Parent() != nil || fn.Signature.TypeParams().Len() != 0 || len(fn.Params) != 1 ||
		Type(fn.Signature.Results().At(0).Type()) != ir.Int64 || len(fn.Blocks) != 3 {
		return nil
	}
	input := fn.Params[0]
	link, payload, ok := chainFields(input.Type())
	if !ok {
		return nil
	}
	entry := fn.Blocks[0]
	if len(entry.Instrs) != 2 || len(entry.Succs) != 2 || len(entry.Preds) != 0 {
		return nil
	}
	cmp, ok := entry.Instrs[0].(*ssa.BinOp)
	branch, branchOK := entry.Instrs[1].(*ssa.If)
	if !ok || !branchOK || branch.Cond != cmp || (cmp.Op != token.EQL && cmp.Op != token.NEQ) {
		return nil
	}
	other := cmp.Y
	if cmp.Y == input {
		other = cmp.X
	} else if cmp.X != input {
		return nil
	}
	constant, ok := other.(*ssa.Const)
	if !ok || constant.Value != nil || !types.Identical(other.Type(), input.Type()) {
		return nil
	}
	base, step := entry.Succs[0], entry.Succs[1]
	if cmp.Op == token.NEQ {
		base, step = step, base
	}
	if base == step || len(base.Instrs) != 1 || len(step.Instrs) < 4 ||
		len(base.Preds) != 1 || len(step.Preds) != 1 || len(base.Succs) != 0 || len(step.Succs) != 0 {
		return nil
	}
	nilReturn, nilOK := base.Instrs[0].(*ssa.Return)
	end := len(step.Instrs) - 1
	stepReturn, stepOK := step.Instrs[end].(*ssa.Return)
	if !nilOK || !stepOK || !invariant(nilReturn.Results[0], ir.Int64) {
		return nil
	}

	chain := &ChainRecursion{Input: input, Base: nilReturn.Results[0], Result: stepReturn.Results[0]}
	available := make(map[ssa.Value]bool)
	called := false
	for i := 0; i < end; i++ {
		switch ins := step.Instrs[i].(type) {
		case *ssa.FieldAddr:
			if ins.X != input || i+1 == end || !readsCell(step.Instrs[i+1], ins) {
				return nil
			}
			load := step.Instrs[i+1].(*ssa.UnOp)
			switch ins.Field {
			case link:
				if chain.Tail != nil {
					return nil
				}
				chain.Tail = load
			case payload:
				if chain.Head != nil {
					return nil
				}
				chain.Head = load
				available[load] = true
			default:
				return nil
			}
			i++ // The following dereference was checked with its field address.
		case *ssa.Call:
			if called || chain.Tail == nil || ins.Call.Value != fn || len(ins.Call.Args) != 1 ||
				ins.Call.Args[0] != chain.Tail {
				return nil
			}
			called = true
			available[ins] = true
			chain.Steps = append(chain.Steps, ins)
		default:
			arithmetic := pureInt64Step(ins, available)
			if arithmetic == nil {
				return nil
			}
			available[arithmetic] = true
			chain.Steps = append(chain.Steps, arithmetic)
		}
	}
	if !called || !loopValue(chain.Result, available) {
		return nil
	}
	return chain
}

func chainFields(t types.Type) (link, payload int, ok bool) {
	pointer, ok := types.Unalias(t).(*types.Pointer)
	if !ok {
		return 0, 0, false
	}
	named, ok := types.Unalias(pointer.Elem()).(*types.Named)
	if !ok {
		return 0, 0, false
	}
	record, ok := named.Underlying().(*types.Struct)
	if !ok || record.NumFields() != 2 {
		return 0, 0, false
	}
	for i := range record.NumFields() {
		next, value := record.Field(i), record.Field(1-i)
		if !next.Embedded() && !value.Embedded() && next.Name() != "_" && value.Name() != "_" &&
			types.Identical(next.Type(), t) && Type(value.Type()) == ir.Int64 {
			return i, 1 - i, true
		}
	}
	return 0, 0, false
}
