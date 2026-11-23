package runtime

import (
	compiler "github.com/frederik-jatzkowski/go-lean/examples/proven/stack_machine_compiler"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

type Type = uint8
type DiagnosticKind = uint8
type Status = uint8

type Compiled struct {
	Code []byte
	Type Type
}

type Diagnostic struct {
	Kind   DiagnosticKind
	Offset uint
}

type State struct {
	PC    uint
	Stack []byte
}

func Compile(source []byte) (Compiled, Diagnostic) {
	result := compiler.CompileBytes(lean.ByteArrayFromBytes(source))
	if result.DiagnosticKind() != compiler.NoDiagnostic {
		return Compiled{}, Diagnostic{Kind: result.DiagnosticKind(), Offset: result.DiagnosticOffset()}
	}
	code := result.Code()
	wire := make([]byte, code.Size())
	for i := range wire {
		wire[i] = code.Get(uint(i)).UnwrapOr(0)
	}
	return Compiled{Code: wire, Type: result.Type()}, Diagnostic{}
}

func Step(code []byte, state State) (State, Status) {
	var stack lean.Array[byte]
	for _, b := range state.Stack {
		stack = stack.Push(b)
	}
	result := compiler.StepBytes(lean.ByteArrayFromBytes(code), state.PC, stack, state.PC%2 == 0)
	if result.Status() != compiler.Continue {
		return state, result.Status()
	}
	return wireState(result.PC(), result.Stack()), compiler.Continue
}

func Run(code []byte) (State, Status) {
	result := compiler.RunBytes(lean.ByteArrayFromBytes(code))
	return wireState(result.PC(), result.Stack()), result.Status()
}

func wireState(pc uint, stack lean.Array[byte]) State {
	state := State{PC: pc, Stack: make([]byte, stack.Size())}
	for i := range state.Stack {
		state.Stack[i] = stack.Get(uint(i)).UnwrapOr(0)
	}
	return state
}
