package compiler

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type runState struct {
	Code   lean.ByteArray
	Result machineResult
}

func runInstruction(_ uint, state runState) lean.FoldControl[runState] {
	result := Step(state.Code, state.Result.State, true)
	return lean.FoldControl[runState]{State: runState{Code: state.Code, Result: result}, Stop: result.Status != Continue}
}

//golean:export
func RunCode(code lean.ByteArray) machineResult {
	initial := machineResult{State: MachineState{PC: 0, Stack: lean.Array[byte]{}}, Status: Continue}
	run := lean.FoldNUntil(code.Size()+1, runState{Code: code, Result: initial}, runInstruction)
	return run.State.Result
}
