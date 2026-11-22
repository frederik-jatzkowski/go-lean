//golean:verify:import bytecode_vm.compiler.vm_spec
package compiler

// State holds the program counter and the active prefix of the stack.
type State struct {
	PC    uint8
	Stack [MaxTokens]byte
	Depth uint8
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

// Step executes one instruction. A halt or error leaves state unchanged.
//
//golean:verify stepMatchesSpec : ∀ (code : Vector UInt8 66) (state : State),
//golean:verify+   Step code state = some (VMModel.step code state)
func Step(code [CodeSize]byte, state State) (State, Status) {
	pc, depth := state.PC, state.Depth
	if pc >= CodeSize || pc%2 != 0 {
		return state, InvalidPC
	}
	if depth > MaxTokens {
		return state, InvalidStack
	}
	op := code[pc]
	if op > Not {
		return state, InvalidOpcode
	}
	if op == Halt {
		return state, Halted
	}
	if pc == CodeSize-2 {
		return state, InvalidPC
	}
	stack := state.Stack
	switch op {
	case Push:
		if depth == MaxTokens {
			return state, InvalidStack
		}
		stack[depth] = code[pc+1]
		depth++
	case Not:
		if depth == 0 {
			return state, InvalidStack
		}
		stack[depth-1] = truthByte(stack[depth-1] == 0)
	default:
		if depth < 2 {
			return state, InvalidStack
		}
		stack[depth-2] = binaryResult(op, stack[depth-1], stack[depth-2])
		depth--
	}
	return State{PC: pc + 2, Stack: stack, Depth: depth}, Continue
}

func binaryResult(op, left, right byte) byte {
	switch op {
	case Add:
		return left + right
	case Sub:
		return left - right
	case Eq:
		return truthByte(left == right)
	case Lt:
		return truthByte(left < right)
	default:
		return truthByte(left != 0 && right != 0)
	}
}

func truthByte(value bool) byte {
	if value {
		return 1
	}
	return 0
}
