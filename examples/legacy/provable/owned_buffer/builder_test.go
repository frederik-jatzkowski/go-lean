package owned_buffer

import "testing"

func TestBuildBeyond256(t *testing.T) {
	targets := make([]uint16, 300)
	for i := range targets {
		targets[i] = uint16(3 * i)
	}
	var builder Builder
	builder.Build(targets)
	if len(builder.code) != len(targets) || len(builder.offsets) != len(targets) {
		t.Fatalf("got %d instructions and %d offsets for %d targets", len(builder.code), len(builder.offsets), len(targets))
	}
	for i, target := range targets {
		if builder.code[i] != (Instruction{Opcode: 1, Target: target}) || builder.offsets[i] != i {
			t.Fatalf("entry %d has instruction %+v and offset %d", i, builder.code[i], builder.offsets[i])
		}
	}
}
