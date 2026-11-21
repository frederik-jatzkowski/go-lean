// Package bytecode_vm demonstrates a verified instruction step and an ordinary Go runner.
package bytecode_vm

type State struct {
	PC          uint8
	Accumulator uint8
}

type Status uint8

const (
	Continue Status = iota
	Halted
	InvalidPC
	InvalidOpcode
)

const (
	OpHalt byte = iota
	OpIncrement
	OpJumpToStart
	OpDecrement
)

// Step executes one instruction. Halt and error statuses preserve the input state.
//
//golean:verify stepReturnsNormally : ∀ (program : Vector UInt8 8) (state : State),
//golean:verify+   ∃ result, Step program state = some result
func Step(program [8]byte, state State) (State, Status) {
	if state.PC >= uint8(len(program)) {
		return state, InvalidPC
	}
	opcode := program[state.PC]
	switch opcode {
	case OpHalt:
		return state, Halted
	case OpJumpToStart:
		state.PC = 0
		return state, Continue
	case OpIncrement, OpDecrement:
		if state.PC == uint8(len(program)-1) {
			return state, InvalidPC
		}
		state.PC++
		if opcode == OpIncrement {
			state.Accumulator++
		} else {
			state.Accumulator--
		}
		return state, Continue
	default:
		return state, InvalidOpcode
	}
}
