package lower

import "testing"

func TestResolveIncomingUsesCurrentBranch(t *testing.T) {
	left := &sourceBlock{}
	right := &sourceBlock{}
	phi := &sourceValue{Kind: phiValue, Values: []*sourceValue{{Name: "right"}, {Name: "left"}}}
	join := &sourceBlock{Preds: []*sourceBlock{right, left}, Instructions: []*sourceValue{phi}}
	input := newInputGraph(&sourceProgram{Functions: []*sourceFunction{{Entry: join}}})
	block := input.ReferenceAt(input.FunctionAt(0), fieldFunctionEntry, 0)
	joined := input.ReferenceAt(block, fieldBlockInstructions, 0)
	leftID, rightID := input.PredecessorAt(block, 1), input.PredecessorAt(block, 0)
	leftValue, rightValue := input.PhiOperandAt(joined, 1), input.PhiOperandAt(joined, 0)
	parent := stateSnapshot{next: 20}
	leftState := parent.Bind(leftValue, 17)
	rightState := parent.Bind(rightValue, 18)

	for _, test := range []struct {
		state                 StateStore
		pred, operand, binder int64
		incoming, bound       bool
	}{
		{leftState, leftID, leftValue, 17, true, true},
		{rightState, rightID, rightValue, 18, true, true},
		{leftState, rightID, rightValue, 0, true, false},
		{parent, leftID, leftValue, 0, true, false},
		{parent, 0, 0, 0, false, false},
	} {
		operand, binder, incoming, bound := resolveIncoming(input, test.state, joined, test.pred)
		if operand != test.operand || binder != test.binder || incoming != test.incoming || bound != test.bound {
			t.Errorf("resolveIncoming for predecessor %d = (%d, %d, %t, %t), want (%d, %d, %t, %t)",
				test.pred, operand, binder, incoming, bound, test.operand, test.binder, test.incoming, test.bound)
		}
	}
}

func TestStateStoreSeparatesFactsAndBindings(t *testing.T) {
	original := stateSnapshot{next: 10}
	bound := original.Bind(9, 8)
	facts := bound.PutFact(9, 1, 3)
	advanced := facts.Advance()
	if original.HasBinding(9) || bound.HasFact(9, 1) ||
		!advanced.HasBinding(9) || advanced.LookupBinding(9) != 8 ||
		!advanced.HasFact(9, 1) || advanced.LookupFact(9, 1) != 3 ||
		facts.NextID() != 10 || advanced.NextID() != 11 {
		t.Fatal("store updates changed an earlier handle or an unrelated namespace")
	}
}
