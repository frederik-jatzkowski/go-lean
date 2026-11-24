package compiler

import (
	"math"

	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

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

type MachineState struct {
	PC    uint
	Stack lean.Array[byte]
}

type machineResult struct {
	State  MachineState
	Status Status
}

//golean:export
func Step(code lean.ByteArray, state MachineState, aligned bool) machineResult {
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

func advance(state MachineState, stack lean.Array[byte]) machineResult {
	return machineResult{State: MachineState{PC: state.PC + 2, Stack: stack}, Status: Continue}
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
