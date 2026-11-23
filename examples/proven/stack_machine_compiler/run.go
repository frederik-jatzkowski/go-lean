package compiler

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type runState struct {
	code   lean.ByteArray
	result machineResult
}

func runInstruction(_ uint, state runState) lean.FoldControl[runState] {
	result := step(state.code, state.result.state, true)
	return lean.FoldControl[runState]{State: runState{code: state.code, result: result}, Stop: result.status != Continue}
}

//golean:export
func runCode(code lean.ByteArray) machineResult {
	initial := machineResult{state: machineState{pc: 0, stack: lean.Array[byte]{}}, status: Continue}
	run := lean.FoldNUntil(code.Size()+1, runState{code: code, result: initial}, runInstruction)
	return run.State.result
}

func RunBytes(code lean.ByteArray) machineResult { return runCode(code) }
