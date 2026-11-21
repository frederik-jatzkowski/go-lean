package compiler

// Run executes code from the initial state until a step halts or fails.
func Run(code [CodeSize]byte) (State, Status) {
	var state State
	for {
		next, status := Step(code, state)
		if status != Continue {
			return next, status
		}
		state = next
	}
}
