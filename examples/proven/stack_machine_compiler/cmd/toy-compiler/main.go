package main

import (
	"fmt"
	"os"

	"github.com/frederik-jatzkowski/go-lean/examples/proven/stack_machine_compiler"
)

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: toy-compiler '<expression>'")
		os.Exit(2)
	}

	compiled, diagnostic := compiler.Compile([]byte(os.Args[1]))
	if diagnostic.Kind != compiler.NoDiagnostic {
		fmt.Fprintf(os.Stderr, "%s at byte %d\n", diagnosticName(diagnostic.Kind), diagnostic.Offset)
		os.Exit(1)
	}

	state, status := compiler.Run(compiled.Code)
	if status != compiler.Halted || len(state.Stack) != 1 {
		fmt.Fprintf(os.Stderr, "VM stopped with status %d and stack depth %d\n", status, len(state.Stack))
		os.Exit(1)
	}
	if compiled.Type == compiler.Bool {
		fmt.Printf("Bool: %t\n", state.Stack[0] != 0)
	} else {
		fmt.Printf("U8: %d\n", state.Stack[0])
	}
}

func diagnosticName(kind compiler.DiagnosticKind) string {
	switch kind {
	case compiler.CodeTooLarge:
		return "CodeTooLarge"
	case compiler.InvalidLexeme:
		return "InvalidLexeme"
	case compiler.SyntaxError:
		return "SyntaxError"
	case compiler.TypeMismatch:
		return "TypeMismatch"
	}
	return "UnexpectedDiagnostic"
}
