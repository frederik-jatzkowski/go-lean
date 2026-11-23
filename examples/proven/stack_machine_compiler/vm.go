package compiler

import (
	"math"

	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

const (
	Continue uint8 = iota
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
	pc    uint
	stack lean.Array[byte]
}

type machineResult struct {
	state  machineState
	status uint8
}

//golean:export
func step(code lean.ByteArray, state machineState, aligned bool) machineResult {
	pc := state.pc
	if !aligned || pc >= code.Size() || code.Size()-pc < 2 {
		return machineResult{state: state, status: InvalidPC}
	}
	op := code.Get(pc).UnwrapOr(Halt)
	if op > Not {
		return machineResult{state: state, status: InvalidOpcode}
	}
	if op == Halt {
		return machineResult{state: state, status: Halted}
	}
	depth := state.stack.Size()
	if op == Push {
		if depth == math.MaxInt {
			return machineResult{state: state, status: InvalidStack}
		}
		return advance(state, state.stack.Push(code.Get(pc+1).UnwrapOr(0)))
	}
	if op == Not {
		if depth == 0 {
			return machineResult{state: state, status: InvalidStack}
		}
		top := state.stack.Get(depth - 1).UnwrapOr(0)
		return advance(state, state.stack.Set(depth-1, truthByte(top == 0)))
	}
	if depth < 2 {
		return machineResult{state: state, status: InvalidStack}
	}
	left := state.stack.Get(depth - 1).UnwrapOr(0)
	right := state.stack.Get(depth - 2).UnwrapOr(0)
	return advance(state, state.stack.Pop().Set(depth-2, binaryResult(op, left, right)))
}

func advance(state machineState, stack lean.Array[byte]) machineResult {
	return machineResult{state: machineState{pc: state.pc + 2, stack: stack}, status: Continue}
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
func StepBytes(code lean.ByteArray, pc uint, stack lean.Array[byte], aligned bool) machineResult {
	return step(code, machineState{pc: pc, stack: stack}, aligned)
}
func (r machineResult) PC() uint                { return r.state.pc }
func (r machineResult) Stack() lean.Array[byte] { return r.state.stack }
func (r machineResult) Status() uint8           { return r.status }
