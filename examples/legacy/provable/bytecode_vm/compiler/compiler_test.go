package compiler

import (
	"bytes"
	"errors"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

func TestCompileAndRun(t *testing.T) {
	for _, tc := range []struct {
		source string
		value  byte
		typ    Type
	}{
		{"0", 0, U8},
		{"255", 255, U8},
		{" \tadd 255\r\n1 ", 0, U8},
		{"sub 2 5", 253, U8},
		{"eq 255 0", 0, Bool},
		{"lt 2 5", 1, Bool},
		{"lt 5 2", 0, Bool},
		{"and false true", 0, Bool},
		{"and eq add 255 1 0 not false", 1, Bool},
	} {
		t.Run(tc.source, func(t *testing.T) {
			compiled, diagnostic := Compile([]byte(tc.source))
			if diagnostic != (Diagnostic{}) || compiled.Type != tc.typ {
				t.Fatalf("Compile returned type %v and %+v, want %v and no diagnostic", compiled.Type, diagnostic, tc.typ)
			}
			state, status := Run(compiled.Code)
			if status != Halted || state.Depth != 1 || state.Stack[0] != tc.value {
				t.Fatalf("Run returned %+v with status %v, want a single value %d at halt", state, status, tc.value)
			}
		})
	}
}

func TestCompileEmitsRightOperandFirst(t *testing.T) {
	compiled, diagnostic := Compile([]byte("sub 2 5"))
	want := [66]byte{1, 5, 1, 2, 3, 0, 0, 0}
	if diagnostic != (Diagnostic{}) || compiled.Code != want || compiled.CodeLen != 8 {
		t.Fatalf("Compile returned %+v and %+v, want eight bytes %v and no diagnostic", compiled, diagnostic, want[:8])
	}
}

func TestExactCapacity(t *testing.T) {
	source := strings.Repeat("not ", 31) + "true"
	source += strings.Repeat(" ", 256-len(source))
	compiled, diagnostic := Compile([]byte(source))
	if diagnostic != (Diagnostic{}) || compiled.CodeLen != 66 || compiled.Type != Bool {
		t.Fatalf("Compile returned %+v and %+v, want 66 bytes and a Bool result", compiled, diagnostic)
	}
	var state State
	for i := range 32 {
		next, status := Step(compiled.Code, state)
		if status != Continue || int(next.PC) != 2*(i+1) {
			t.Fatalf("instruction %d returned PC %d and status %v", i, next.PC, status)
		}
		state = next
	}
	next, status := Step(compiled.Code, state)
	if status != Halted || next != state || state.Depth != 1 || state.Stack[0] != 0 {
		t.Fatalf("Halt returned %+v and status %v, want one live byte with value 0", next, status)
	}
}

func TestCompileDiagnostics(t *testing.T) {
	for _, tc := range []struct {
		name   string
		source []byte
		want   Diagnostic
	}{
		{"nil", nil, Diagnostic{SyntaxError, 0}},
		{"empty", []byte{}, Diagnostic{SyntaxError, 0}},
		{"whitespace only", []byte(" \t\r\n"), Diagnostic{SyntaxError, 4}},
		{"non-ASCII", []byte{0x80}, Diagnostic{InvalidLexeme, 0}},
		{"invalid word", []byte("add maybe 1"), Diagnostic{InvalidLexeme, 4}},
		{"case sensitive", []byte("False"), Diagnostic{InvalidLexeme, 0}},
		{"lexeme too long", []byte("not foolish"), Diagnostic{InvalidLexeme, 4}},
		{"literal overflow", []byte("256"), Diagnostic{InvalidLexeme, 0}},
		{"leading zero", []byte("00"), Diagnostic{InvalidLexeme, 0}},
		{"missing operand at full length", []byte("add 1" + strings.Repeat(" ", 251)), Diagnostic{SyntaxError, 256}},
		{"extra expression", []byte("true false "), Diagnostic{SyntaxError, 11}},
		{"source length wins over bad lexeme", []byte("?" + strings.Repeat(" ", 256)), Diagnostic{SourceTooLong, 256}},
		{"valid 33rd token", []byte(strings.Repeat("0 ", 32) + "0"), Diagnostic{TooManyTokens, 64}},
		{"invalid 33rd token", []byte(strings.Repeat("0 ", 32) + "?"), Diagnostic{InvalidLexeme, 64}},
		{"type mismatch", []byte("  add true 1"), Diagnostic{TypeMismatch, 2}},
		{"right mismatch before left", []byte("and add true 1 sub false 2"), Diagnostic{TypeMismatch, 15}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			compiled, diagnostic := Compile(tc.source)
			if diagnostic != tc.want || compiled != (Compiled{}) {
				t.Fatalf("Compile returned %+v and %+v, want zero result and %+v", compiled, diagnostic, tc.want)
			}
		})
	}
}

func TestStepRejectsRawErrorsWithoutChangingState(t *testing.T) {
	for _, tc := range []struct {
		name   string
		code   [66]byte
		state  State
		status Status
	}{
		{"odd PC", [66]byte{}, State{PC: 1}, InvalidPC},
		{"PC past code", [66]byte{}, State{PC: 66}, InvalidPC},
		{"PC before depth", [66]byte{}, State{PC: 1, Depth: 33}, InvalidPC},
		{"invalid depth", [66]byte{}, State{Depth: 33}, InvalidStack},
		{"depth before opcode", [66]byte{255}, State{Depth: 33}, InvalidStack},
		{"unknown opcode", [66]byte{255}, State{Stack: [32]byte{9}, Depth: 1}, InvalidOpcode},
		{"unknown at final slot", [66]byte{64: 255}, State{PC: 64}, InvalidOpcode},
		{"unary underflow", [66]byte{Not}, State{}, InvalidStack},
		{"binary underflow", [66]byte{Sub}, State{Stack: [32]byte{9}, Depth: 1}, InvalidStack},
		{"overflow", [66]byte{Push, 7}, State{Depth: 32}, InvalidStack},
		{"final slot before underflow", [66]byte{64: Add}, State{PC: 64}, InvalidPC},
	} {
		t.Run(tc.name, func(t *testing.T) {
			next, status := Step(tc.code, tc.state)
			if status != tc.status || next != tc.state {
				t.Fatalf("Step returned %+v with status %v, want unchanged state and status %v", next, status, tc.status)
			}
		})
	}
}

func TestRawBooleanInstructionsNormalize(t *testing.T) {
	code := [66]byte{And, 255, Not, 255, Halt, 255}
	input := State{Stack: [32]byte{9, 2, 3, 19}, Depth: 3}
	combined, status := Step(code, input)
	want := State{PC: 2, Stack: [32]byte{9, 1, 3, 19}, Depth: 2}
	if status != Continue || combined != want {
		t.Fatalf("And returned %+v with status %v, want %+v and Continue", combined, status, want)
	}
	negated, status := Step(code, combined)
	want.PC = 4
	want.Stack[1] = 0
	if status != Continue || negated != want {
		t.Fatalf("Not returned %+v with status %v, want %+v and Continue", negated, status, want)
	}
	final, status := Step(code, negated)
	if status != Halted || final != negated {
		t.Fatalf("Halt returned %+v with status %v, want unchanged state and Halted", final, status)
	}
}

func TestDemo(t *testing.T) {
	binary := filepath.Join(t.TempDir(), "toy-compiler")
	if runtime.GOOS == "windows" {
		binary += ".exe"
	}
	if output, err := exec.Command("go", "build", "-o", binary, "./cmd/toy-compiler").CombinedOutput(); err != nil {
		t.Fatalf("building demo: %v\n%s", err, output)
	}
	for _, tc := range []struct {
		name   string
		args   []string
		stdout string
		stderr string
		exit   int
	}{
		{"numeric", []string{"sub 2 5"}, "U8: 253\n", "", 0},
		{"boolean", []string{"and eq add 255 1 0 not false"}, "Bool: true\n", "", 0},
		{"diagnostic", []string{"add 1 true"}, "", "TypeMismatch at byte 0\n", 1},
		{"usage", nil, "", "usage: toy-compiler '<expression>'\n", 2},
	} {
		t.Run(tc.name, func(t *testing.T) {
			command := exec.Command(binary, tc.args...)
			var stdout, stderr bytes.Buffer
			command.Stdout, command.Stderr = &stdout, &stderr
			exit := 0
			if err := command.Run(); err != nil {
				var exitErr *exec.ExitError
				if !errors.As(err, &exitErr) {
					t.Fatal(err)
				}
				exit = exitErr.ExitCode()
			}
			if exit != tc.exit || stdout.String() != tc.stdout || stderr.String() != tc.stderr {
				t.Fatalf("demo exited %d with stdout %q and stderr %q, want %d, %q, %q",
					exit, stdout.String(), stderr.String(), tc.exit, tc.stdout, tc.stderr)
			}
		})
	}
}
