package transpile_test

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func TestFocusedPackageModelsComposeProofs(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "lakefile.toml"), `name = "Canonical"
[[lean_lib]]
name = "Canonical"
roots = [
  # BEGIN go-lean managed roots
  # END go-lean managed roots
]
`)
	writeFile(t, filepath.Join(dir, "parser", "parser.go"), `package parser

//golean:export
//golean:verify parseValue : ∀ (value : Int64), Parse value = ⟨value⟩
func Parse(value int64) AST { return node(value) }
`)
	writeFile(t, filepath.Join(dir, "parser", "node.go"), `package parser

type AST struct { Value int64 }

func node(value int64) AST { return AST{Value: value} }
`)
	writeFile(t, filepath.Join(dir, "parser", "parser_proofs.lean"), `import parser.parser_gen

namespace GoLean.«example.test/sample/parser».parser.Proofs
theorem parseValue : Laws.parseValue := fun _ => rfl
end GoLean.«example.test/sample/parser».parser.Proofs
`)
	writeFile(t, filepath.Join(dir, "compiler", "compiler.go"), `package compiler

import "example.test/sample/parser"

//golean:verify compileValue : ∀ (value : Int64), Compile value = ⟨value⟩
func Compile(value int64) parser.AST { return parser.Parse(value) }
`)
	writeFile(t, filepath.Join(dir, "compiler", "compiler_proofs.lean"), `import compiler.compiler_gen
import parser.parser_proofs

namespace GoLean.«example.test/sample/compiler».compiler.Proofs
theorem compileValue : Laws.compileValue := by
  intro value
  unfold Compile
  rw [GoLean.«example.test/sample/parser».parser.Proofs.parseValue]
end GoLean.«example.test/sample/compiler».compiler.Proofs
`)

	readModel := func(name string) []byte {
		t.Helper()
		model, err := os.ReadFile(filepath.Join(dir, name, name+"_model.lean"))
		if err != nil {
			t.Fatal(err)
		}
		return model
	}
	lake, lakeErr := exec.LookPath("lake")
	parserTargets, err := transpile.ReconcilePattern(dir, "./parser")
	if err != nil {
		t.Fatal(err)
	}
	parserModel := readModel("parser")
	if lakeErr == nil {
		checkLake(t, lake, dir, "", parserTargets...)
	}
	compilerTargets, err := transpile.ReconcilePattern(dir, "./compiler")
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(parserModel, readModel("parser")) {
		t.Fatal("generating a caller changed the standalone parser model")
	}
	compilerModel := string(readModel("compiler"))
	if !strings.Contains(compilerModel, "import «parser».«parser_model»") ||
		!strings.Contains(compilerModel, `GoLean.«example.test/sample/parser».«AST»`) ||
		!strings.Contains(compilerModel, `GoLean.«example.test/sample/parser».«Parse»`) ||
		strings.Contains(compilerModel, "structure ") || strings.Count(compilerModel, "\ndef ") != 1 {
		t.Fatalf("expected the compiler to import and reuse the parser model:\n%s", compilerModel)
	}
	if lakeErr != nil {
		t.Skip("Lake is unavailable on PATH")
	}
	checkLake(t, lake, dir, "", compilerTargets...)
}
