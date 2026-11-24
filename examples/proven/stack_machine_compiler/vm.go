package compiler

import (
	model "github.com/frederik-jatzkowski/go-lean/examples/proven/stack_machine_compiler/model"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

// State holds the program counter and the live operands, with the top at the end.
type State struct {
	PC    uint
	Stack []byte
}

// Step executes one complete instruction pair.
func Step(code []byte, state State) (State, model.Status) {
	var stack lean.Array[byte]
	for _, b := range state.Stack {
		stack = stack.Push(b)
	}
	result := model.Step(lean.ByteArrayFromBytes(code), model.MachineState{PC: state.PC, Stack: stack}, state.PC%2 == 0)
	if result.Status != model.Continue {
		return state, result.Status
	}
	return wireState(result.State.PC, result.State.Stack), model.Continue
}

func wireState(pc uint, stack lean.Array[byte]) State {
	next := State{PC: pc, Stack: make([]byte, stack.Size())}
	for i := range next.Stack {
		next.Stack[i] = stack.Get(uint(i)).UnwrapOr(0)
	}
	return next
}
