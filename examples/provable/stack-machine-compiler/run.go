package compiler

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type runState struct {
	Code   lean.ByteArray
	Result machineResult
}

func runInstruction(_ uint, state runState) lean.FoldControl[runState] {
	result := step(state.Code, state.Result.State, true)
	return lean.FoldControl[runState]{State: runState{Code: state.Code, Result: result}, Stop: result.Status != Continue}
}

//golean:export
func runCode(code lean.ByteArray) machineResult {
	initial := machineResult{State: machineState{PC: 0, Stack: lean.Array[byte]{}}, Status: Continue}
	run := lean.FoldNUntil(code.Size()+1, runState{Code: code, Result: initial}, runInstruction)
	return run.State.Result
}

// Run executes code from the initial state until a step halts or fails.
func Run(code []byte) (State, Status) {
	result := runCode(lean.ByteArrayFromBytes(code))
	return wireState(result.State), result.Status
}
