package compiler

import (
	model "github.com/frederik-jatzkowski/go-lean/examples/proven/stack_machine_compiler/model"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

// Run executes code from the initial state until a step halts or fails.
func Run(code []byte) (State, model.Status) {
	result := model.RunCode(lean.ByteArrayFromBytes(code))
	return wireState(result.State.PC, result.State.Stack), result.Status
}
