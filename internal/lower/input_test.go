package lower

import (
	"path/filepath"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/subset"
)

func TestFromSSAWithInMemoryInput(t *testing.T) {
	typ := &sourceType{Model: ir.Int64}
	value := &sourceValue{Kind: constantValue, Type: typ, Text: "42"}
	ret := &sourceValue{Kind: returnValue, Values: []*sourceValue{value}}
	fn := &sourceFunction{Name: "Answer", Package: "sample", Entry: &sourceBlock{Instructions: []*sourceValue{ret}},
		Results: []*sourceType{typ}}
	input := newInputGraph(&sourceProgram{Package: "sample", Functions: []*sourceFunction{fn}})
	program := FromSSA(input, "answers", 64)
	if len(program.Functions) != 1 {
		t.Fatalf("got %d functions, want 1", len(program.Functions))
	}
	out := program.Functions[0]
	if out.Symbol != (ir.Symbol{Package: "sample", File: "answers", Name: "Answer"}) ||
		out.Result != ir.Int64 || out.Body.Result != (ir.Return{Value: ir.IntLiteral{Value: "42", Type: ir.Int64}}) {
		t.Fatalf("unexpected lowering: %#v", out)
	}
}

func TestCheckedInputExposesOrderAndMetadata(t *testing.T) {
	programs, err := gosource.Load(filepath.Join("..", "..", "examples", "provable", "multi_result"))
	if err != nil {
		t.Fatal(err)
	}
	if len(programs) != 1 {
		t.Fatalf("want one checked source file, got %d", len(programs))
	}
	checked, err := subset.Check(programs[0])
	if err != nil {
		t.Fatal(err)
	}
	input := NewInput(checked)
	second := NewInput(checked)
	functions := make(map[string]int64)
	for i := int64(0); i < input.FunctionCount(); i++ {
		id := input.FunctionAt(i)
		if id <= 0 || input.FunctionOrder(id) != i || second.FunctionAt(i) != id {
			t.Fatalf("function position %d has inconsistent ID %d", i, id)
		}
		functions[input.FieldText(id, fieldFunctionName)] = id
	}
	if input.FunctionOrder(functions["Divide"]) >= input.FunctionOrder(functions["Reorder"]) {
		t.Fatal("Divide must precede Reorder")
	}
	if input.FunctionAt(-1) != 0 || input.FunctionAt(input.FunctionCount()) != 0 ||
		input.FunctionOrder(0) != -1 || input.FieldText(0, fieldFunctionName) != "" {
		t.Fatal("absent queries did not return their neutral values")
	}
	counted := input.ReferenceAt(functions["Count"], fieldFunctionCounted, 0)
	loop := input.ReferenceAt(counted, fieldCountedStructured, 0)
	if counted == 0 || !input.HasStructuredLoop(loop) || input.LoopStateCount(loop) < 2 {
		t.Fatal("Count lost its structured loop state")
	}
	if input.ReferenceAt(functions["Chain"], fieldFunctionChain, 0) == 0 ||
		input.ReferenceAt(functions["Double"], fieldFunctionBuild, 0) == 0 {
		t.Fatal("specialized source metadata is missing")
	}

	seen := make(map[int64]bool)
	var todo []int64
	for i := int64(0); i < input.FunctionCount(); i++ {
		todo = append(todo, input.ReferenceAt(input.FunctionAt(i), fieldFunctionEntry, 0))
	}
	hasPhi := false
	for len(todo) > 0 {
		block := todo[len(todo)-1]
		todo = todo[:len(todo)-1]
		if seen[block] {
			continue
		}
		seen[block] = true
		for i := int64(0); i < input.ReferenceCount(block, fieldBlockInstructions); i++ {
			phi := input.ReferenceAt(block, fieldBlockInstructions, i)
			if input.HasOrderedCall(phi) {
				target := input.FunctionOrder(input.CallTarget(phi))
				owner := input.FunctionOrder(input.CallOwner(phi))
				if target < 0 || target >= owner {
					t.Fatalf("call %d does not follow dependency order", phi)
				}
			}
			for j := int64(0); j < input.OrdinaryOperandCount(phi); j++ {
				if !input.HasRecord(input.OrdinaryOperandAt(phi, j)) || !input.OperandDominates(phi, j) {
					t.Fatalf("operand %d does not dominate instruction %d", j, phi)
				}
			}
			if input.PhiBlock(phi) != block {
				continue
			}
			hasPhi = true
			if input.PhiOperandCount(phi) != input.PredecessorCount(block) {
				t.Fatal("phi operand count differs from predecessor count")
			}
			for j := int64(0); j < input.PredecessorCount(block); j++ {
				pred := input.PredecessorAt(block, j)
				if !input.HasIncoming(phi, pred) || input.Incoming(phi, pred) != input.PhiOperandAt(phi, j) {
					t.Fatalf("phi %d does not preserve predecessor position %d", phi, j)
				}
			}
		}
		for i := int64(0); i < input.ReferenceCount(block, fieldBlockSuccs); i++ {
			todo = append(todo, input.ReferenceAt(block, fieldBlockSuccs, i))
		}
	}
	if !hasPhi {
		t.Fatal("expected a phi in Divide")
	}
}
