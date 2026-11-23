package compiler

import (
	"math"

	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

// State holds the program counter and the live operands, with the top at the end.
type State struct {
	PC    uint
	Stack []byte
}

type Status uint8

const (
	Continue Status = iota
	Halted
	InvalidPC
	InvalidStack
	InvalidOpcode
)

const (
	Halt byte = iota
	Push
	Add
	Sub
	Eq
	Lt
	And
	Not
)

type machineState struct {
	PC    uint
	Stack lean.Array[byte]
}

type machineResult struct {
	State  machineState
	Status Status
}

// Step executes one complete instruction pair.
func Step(code []byte, state State) (State, Status) {
	var stack lean.Array[byte]
	for _, b := range state.Stack {
		stack = stack.Push(b)
	}
	result := step(lean.ByteArrayFromBytes(code), machineState{PC: state.PC, Stack: stack}, state.PC%2 == 0)
	if result.Status != Continue {
		return state, result.Status
	}
	return wireState(result.State), Continue
}

func wireState(state machineState) State {
	next := State{PC: state.PC, Stack: make([]byte, state.Stack.Size())}
	for i := range next.Stack {
		next.Stack[i] = state.Stack.Get(uint(i)).UnwrapOr(0)
	}
	return next
}

//golean:export
func step(code lean.ByteArray, state machineState, aligned bool) machineResult {
	pc := state.PC
	if !aligned || pc >= code.Size() || code.Size()-pc < 2 {
		return machineResult{State: state, Status: InvalidPC}
	}
	op := code.Get(pc).UnwrapOr(Halt)
	if op > Not {
		return machineResult{State: state, Status: InvalidOpcode}
	}
	if op == Halt {
		return machineResult{State: state, Status: Halted}
	}
	depth := state.Stack.Size()
	if op == Push {
		if depth == math.MaxInt {
			return machineResult{State: state, Status: InvalidStack}
		}
		return advance(state, state.Stack.Push(code.Get(pc+1).UnwrapOr(0)))
	}
	if op == Not {
		if depth == 0 {
			return machineResult{State: state, Status: InvalidStack}
		}
		top := state.Stack.Get(depth - 1).UnwrapOr(0)
		return advance(state, state.Stack.Set(depth-1, truthByte(top == 0)))
	}
	if depth < 2 {
		return machineResult{State: state, Status: InvalidStack}
	}
	left := state.Stack.Get(depth - 1).UnwrapOr(0)
	right := state.Stack.Get(depth - 2).UnwrapOr(0)
	return advance(state, state.Stack.Pop().Set(depth-2, binaryResult(op, left, right)))
}

func advance(state machineState, stack lean.Array[byte]) machineResult {
	return machineResult{State: machineState{PC: state.PC + 2, Stack: stack}, Status: Continue}
}

func binaryResult(op, left, right byte) byte {
	if op == Add {
		return left + right
	}
	if op == Sub {
		return left - right
	}
	if op == Eq {
		return truthByte(left == right)
	}
	if op == Lt {
		return truthByte(left < right)
	}
	return truthByte(left != 0 && right != 0)
}

func truthByte(value bool) byte {
	if value {
		return 1
	}
	return 0
}
