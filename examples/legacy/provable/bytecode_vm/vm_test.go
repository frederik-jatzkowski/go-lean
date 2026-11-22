package bytecode_vm

import "testing"

func TestStep(t *testing.T) {
	for _, tc := range []struct {
		name    string
		program [8]byte
		start   State
		want    State
		status  Status
	}{
		{"increment wraps", [8]byte{OpIncrement}, State{Accumulator: 255}, State{PC: 1}, Continue},
		{"decrement wraps", [8]byte{OpDecrement}, State{}, State{PC: 1, Accumulator: 255}, Continue},
		{"out of bounds", [8]byte{}, State{PC: 8, Accumulator: 5}, State{PC: 8, Accumulator: 5}, InvalidPC},
		{"last increment", [8]byte{7: OpIncrement}, State{PC: 7, Accumulator: 5}, State{PC: 7, Accumulator: 5}, InvalidPC},
		{"last decrement", [8]byte{7: OpDecrement}, State{PC: 7, Accumulator: 5}, State{PC: 7, Accumulator: 5}, InvalidPC},
		{"last halt", [8]byte{}, State{PC: 7, Accumulator: 5}, State{PC: 7, Accumulator: 5}, Halted},
		{"last jump", [8]byte{7: OpJumpToStart}, State{PC: 7, Accumulator: 5}, State{Accumulator: 5}, Continue},
		{"unknown opcode", [8]byte{255}, State{Accumulator: 5}, State{Accumulator: 5}, InvalidOpcode},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, status := Step(tc.program, tc.start)
			if got != tc.want || status != tc.status {
				t.Fatalf("Step returned (%+v, %v), want (%+v, %v)", got, status, tc.want, tc.status)
			}
		})
	}
}

func TestRun(t *testing.T) {
	for _, tc := range []struct {
		name    string
		program [8]byte
		want    State
		status  Status
	}{
		{"demo halts", [8]byte{OpIncrement, OpIncrement, OpHalt}, State{PC: 2, Accumulator: 2}, Halted},
		{"stops at invalid opcode", [8]byte{OpIncrement, 255}, State{PC: 1, Accumulator: 1}, InvalidOpcode},
		{"stops at invalid fallthrough", [8]byte{
			OpIncrement, OpIncrement, OpIncrement, OpIncrement,
			OpIncrement, OpIncrement, OpIncrement, OpIncrement,
		}, State{PC: 7, Accumulator: 7}, InvalidPC},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, status := Run(tc.program)
			if got != tc.want || status != tc.status {
				t.Fatalf("Run returned (%+v, %v), want (%+v, %v)", got, status, tc.want, tc.status)
			}
		})
	}
}

func TestLoopingProgramPrefix(t *testing.T) {
	program := [8]byte{OpIncrement, OpJumpToStart}
	var state State
	for range 32 {
		next, status := Step(program, state)
		if status != Continue {
			t.Fatalf("Step at %+v returned terminal status %v", state, status)
		}
		state = next
	}
	if state != (State{Accumulator: 16}) {
		t.Fatalf("32 steps returned %+v, want PC 0 and accumulator 16", state)
	}
}
