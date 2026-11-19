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
	Input   *ssa.Parameter
	Element ir.Type
	Head    *ssa.UnOp
	Tail    *ssa.UnOp
	Base    []ssa.Value
	Steps   []ssa.Value
	Result  []ssa.Value
}

func checkChainRecursion(fn *ssa.Function) *ChainRecursion {
	if fn.Parent() != nil || fn.Signature.TypeParams().Len() != 0 || len(fn.Params) == 0 ||
		len(fn.Blocks) != 3 {
		return nil
	}
	input := fn.Params[0]
	link, ok := chainLink(input.Type())
	for result := range fn.Signature.Results().Variables() {
		if !Type(result.Type()).IsInteger() {
			return nil
		}
	}
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
	if !nilOK || !stepOK {
		return nil
	}

	for _, value := range nilReturn.Results {
		if !invariant(value, Type(value.Type())) {
			return nil
		}
	}
	chain := &ChainRecursion{Input: input, Element: ir.Int64, Base: nilReturn.Results, Result: stepReturn.Results}
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
			default:
				element := Type(load.Type())
				if chain.Head != nil || !element.IsInteger() {
					return nil
				}
				chain.Head = load
				chain.Element = element
				available[load] = true
			}
			i++ // The following dereference was checked with its field address.
		case *ssa.Call:
			if called || chain.Tail == nil || ins.Call.Value != fn || len(ins.Call.Args) != len(fn.Params) ||
				ins.Call.Args[0] != chain.Tail {
				return nil
			}
			for i, arg := range ins.Call.Args[1:] {
				if arg != fn.Params[i+1] {
					return nil
				}
			}
			called = true
			available[ins] = true
			chain.Steps = append(chain.Steps, ins)
		case *ssa.Extract:
			call, ok := ins.Tuple.(*ssa.Call)
			if !ok || call.Call.Value != fn || !available[call] {
				return nil
			}
			available[ins] = true
			chain.Steps = append(chain.Steps, ins)
		default:
			value, ok := ins.(ssa.Value)
			if !ok {
				return nil
			}
			typ := Type(value.Type())
			if !typ.IsInteger() {
				return nil
			}
			arithmetic := integerStep(ins, available, typ)
			if arithmetic == nil {
				return nil
			}
			available[arithmetic] = true
			chain.Steps = append(chain.Steps, arithmetic)
		}
	}
	if !called {
		return nil
	}
	for _, value := range chain.Result {
		if !available[value] && !invariant(value, Type(value.Type())) {
			return nil
		}
	}
	return chain
}

func chainLink(t types.Type) (link int, ok bool) {
	pointer, ok := types.Unalias(t).(*types.Pointer)
	if !ok {
		return 0, false
	}
	named, ok := types.Unalias(pointer.Elem()).(*types.Named)
	if !ok {
		return 0, false
	}
	record, ok := named.Underlying().(*types.Struct)
	if !ok {
		return 0, false
	}
	link = -1
	for i := range record.NumFields() {
		field := record.Field(i)
		if !field.Embedded() && field.Name() != "_" && types.Identical(field.Type(), t) {
			if link >= 0 {
				return 0, false
			}
			link = i
		}
	}
	return link, link >= 0
}
