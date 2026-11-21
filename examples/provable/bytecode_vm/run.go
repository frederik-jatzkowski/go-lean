package bytecode_vm

// Run starts at PC zero and returns the state and status of the first terminal step.
func Run(program [8]byte) (State, Status) {
	var state State
	for {
		next, status := Step(program, state)
		if status != Continue {
			return next, status
		}
		state = next
	}
}
