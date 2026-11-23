package compiler

import (
	"bytes"
	"errors"
	"math"
	"os/exec"
	"path/filepath"
	"runtime"
	"slices"
	"strconv"
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
			if status != Halted || len(state.Stack) != 1 || state.Stack[0] != tc.value {
				t.Fatalf("Run returned %+v with status %v, want a single value %d at halt", state, status, tc.value)
			}
		})
	}
}

func TestDecimalLiterals(t *testing.T) {
	for value := range 256 {
		compiled, diagnostic := Compile([]byte(strconv.Itoa(value)))
		if diagnostic != (Diagnostic{}) || compiled.Type != U8 ||
			!bytes.Equal(compiled.Code, []byte{Push, byte(value), Halt, 0}) {
			t.Fatalf("decimal %d compiled to %+v with diagnostic %+v", value, compiled, diagnostic)
		}
	}
}

func TestCompileEmitsRightOperandFirst(t *testing.T) {
	compiled, diagnostic := Compile([]byte("sub sub 9 2 sub 5 1"))
	want := []byte{Push, 1, Push, 5, Sub, 0, Push, 2, Push, 9, Sub, 0, Sub, 0, Halt, 0}
	if diagnostic != (Diagnostic{}) || !bytes.Equal(compiled.Code, want) {
		t.Fatalf("Compile returned %+v and %+v, want %v and no diagnostic", compiled, diagnostic, want)
	}
}

func TestVariableSize(t *testing.T) {
	source := strings.Repeat("sub ", 80) + "1" + strings.Repeat(" 1", 80)
	compiled, d := Compile([]byte(source))
	if d != (Diagnostic{}) || len(compiled.Code) != 324 {
		t.Fatal(d, len(compiled.Code))
	}
	var st State
	for i := 0; i < 81; i++ {
		var status Status
		st, status = Step(compiled.Code, st)
		if status != Continue {
			t.Fatal(i, status)
		}
	}
	if len(st.Stack) != 81 {
		t.Fatal(len(st.Stack))
	}
	st, status := Run(compiled.Code)
	if status != Halted || st.PC != 322 || !bytes.Equal(st.Stack, []byte{177}) {
		t.Fatal(st, status)
	}
}
func TestCodeFits(t *testing.T) {
	const last = (math.MaxInt - 2) / 2
	if !codeFits(last) || codeFits(last+1) || codeFits(^uint(0)) {
		t.Fatal("incorrect output-size boundary")
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
		{"wide offset", []byte(strings.Repeat(" ", 70000) + "?"), Diagnostic{InvalidLexeme, 70000}},
		{"non-ASCII", []byte{0x80}, Diagnostic{InvalidLexeme, 0}},
		{"invalid word", []byte("add maybe 1"), Diagnostic{InvalidLexeme, 4}},
		{"case sensitive", []byte("False"), Diagnostic{InvalidLexeme, 0}},
		{"lexeme too long", []byte("not foolish"), Diagnostic{InvalidLexeme, 4}},
		{"literal overflow", []byte("256"), Diagnostic{InvalidLexeme, 0}},
		{"leading zero", []byte("00"), Diagnostic{InvalidLexeme, 0}},
		{"missing operand at full length", []byte("add 1" + strings.Repeat(" ", 251)), Diagnostic{SyntaxError, 256}},
		{"extra expression", []byte("true false "), Diagnostic{SyntaxError, 11}},
		{"extra expressions", []byte(strings.Repeat("0 ", 32) + "0"), Diagnostic{SyntaxError, 65}},
		{"invalid 33rd token", []byte(strings.Repeat("0 ", 32) + "?"), Diagnostic{InvalidLexeme, 64}},
		{"type mismatch", []byte("  add true 1"), Diagnostic{TypeMismatch, 2}},
		{"syntax before type mismatch", []byte("add true 1 2"), Diagnostic{SyntaxError, 12}},
		{"two unary type errors", []byte("and not 1 not 2"), Diagnostic{TypeMismatch, 10}},
		{"right mismatch before left", []byte("and add true 1 sub false 2"), Diagnostic{TypeMismatch, 15}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			compiled, diagnostic := Compile(tc.source)
			if diagnostic != tc.want || compiled.Type != 0 || compiled.Code != nil {
				t.Fatalf("Compile returned %+v and %+v, want zero result and %+v", compiled, diagnostic, tc.want)
			}
		})
	}
}

func TestRawVM(t *testing.T) {
	for _, tc := range []struct {
		name   string
		code   []byte
		pc     uint
		status Status
	}{
		{"empty", nil, 0, InvalidPC}, {"odd PC", []byte{Halt, 0}, 1, InvalidPC}, {"extreme PC", []byte{Push, 0}, ^uint(0) - 1, InvalidPC},
		{"lone halt", []byte{Halt}, 0, InvalidPC}, {"truncated unknown", []byte{255}, 0, InvalidPC},
		{"unknown", []byte{255, 0}, 0, InvalidOpcode}, {"unary underflow", []byte{Not, 0}, 0, InvalidStack},
		{"binary underflow", []byte{Sub, 0}, 0, InvalidStack}, {"early halt", []byte{Halt, 2, 255}, 0, Halted},
	} {
		t.Run(tc.name, func(t *testing.T) {
			state := State{PC: tc.pc}
			next, status := Step(tc.code, state)
			if status != tc.status || next.PC != state.PC || next.Stack != nil {
				t.Fatal(next, status)
			}
			if tc.pc == 0 {
				final, status := Run(tc.code)
				if status != tc.status || final.PC != 0 || len(final.Stack) != 0 {
					t.Fatal(final, status)
				}
			}
		})
	}
	for _, code := range [][]byte{{Push, 7}, {Push, 7, Halt}} {
		state, status := Run(code)
		if status != InvalidPC || state.PC != 2 || !bytes.Equal(state.Stack, []byte{7}) {
			t.Fatal(state, status)
		}
	}
}
func TestRawBooleanInstructionsNormalize(t *testing.T) {
	code := []byte{And, 255, Not, 255, Halt, 255}
	input := State{Stack: []byte{9, 2, 3}}
	combined, status := Step(code, input)
	if status != Continue || combined.PC != 2 || !slices.Equal(combined.Stack, []byte{9, 1}) || !slices.Equal(input.Stack, []byte{9, 2, 3}) {
		t.Fatal(combined, input, status)
	}
	negated, status := Step(code, combined)
	if status != Continue || negated.PC != 4 || !slices.Equal(negated.Stack, []byte{9, 0}) || !slices.Equal(combined.Stack, []byte{9, 1}) {
		t.Fatal(negated, combined, status)
	}
	final, status := Step(code, negated)
	if status != Halted || final.PC != negated.PC || !slices.Equal(final.Stack, negated.Stack) {
		t.Fatal(final, status)
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
