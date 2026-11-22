package transpile_test

import (
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func TestScopedLawsAndImports(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "doc.go"), `// Package sample exercises file and package scope.
//
//golean:verify:import late
//golean:verify:import input_gen
//golean:verify final : GoLean.«example.test/sample».input.«Value$Read» 0 = Late.expected
package sample
`)
	writeFile(t, filepath.Join(dir, "input.go"), `//golean:verify:import «late»
package sample

import "example.test/sample/port"

//golean:verify typeLaw : «Value$Read» 0 = Late.expected
type Value int64

//golean:verify methodLaw : ∀ input, «Value$Read» input = 1
func (Value) Read() int64 { return 1 }

//golean:export
func Apply(s port.Service) int64 { return s.Read() }

//golean:abstract port.Mirror
//golean:verify abstractLaw : True
func Call(x int64) int64 { return port.Mirror(x) }
`)
	writeFile(t, filepath.Join(dir, "port", "port.go"), `//golean:assume:import early
package port

//golean:assume contract : ∀ s, Read s = Early.expected
type Service interface { Read() int64 }

//golean:assume contract : ∀ x, Mirror x = Early.expected
func Mirror(x int64) int64 { return 1 }
`)
	writeFile(t, filepath.Join(dir, "early.lean"), "def Early.expected : Int64 := 1\n")
	writeFile(t, filepath.Join(dir, "late.lean"), "import input_gen\ndef Late.expected : Int64 := GoLean.«example.test/sample».input.«Value$Read» 0\n")
	writeFile(t, filepath.Join(dir, "input_proofs.lean"), `import input_laws
namespace GoLean.«example.test/sample».input.Proofs
theorem typeLaw : Laws.typeLaw := rfl
theorem methodLaw : Laws.methodLaw := fun _ => rfl
theorem abstractLaw : Laws.abstractLaw := fun _ => True.intro
end GoLean.«example.test/sample».input.Proofs
`)
	const docHeader = "import doc_laws\nnamespace GoLean.«example.test/sample».doc.Proofs\n"
	docProofs := filepath.Join(dir, "doc_proofs.lean")
	writeFile(t, docProofs, docHeader+"theorem final : Laws.final := rfl\n")
	writeFile(t, filepath.Join(dir, "lakefile.toml"), `name = "Scoped"
[[lean_lib]]
name = "Scoped"
roots = ["early", "late", "sample_model", "port.port_model", "input_gen", "input_laws", "input_proofs", "input_verify", "doc_laws", "doc_proofs", "doc_verify"]
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	models := make(map[string]string)
	for _, output := range outputs {
		models[filepath.Base(output.Path)] = output.Source
	}
	if _, exists := models["doc_gen.lean"]; exists {
		t.Fatal("a law-only file generated an operation model")
	}
	if model := models["sample_model.lean"]; strings.Count(model, "import «early»\n") != 1 || strings.Contains(model, "import «late»\n") {
		t.Fatalf("unexpected model imports:\n%s", model)
	}
	if laws := models["input_laws.lean"]; strings.Count(laws, "import «late»\n") != 1 || strings.Count(laws, "import «input_gen»\n") != 1 {
		t.Fatalf("expected deduplicated verification imports:\n%s", laws)
	}
	if err := transpile.Write(outputs); err != nil {
		t.Fatal(err)
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("Lake is unavailable on PATH")
	}
	checkLake(t, lake, dir, "")
	for _, test := range []struct{ name, body, diagnostic string }{
		{"missing", "", "must be declared in doc_proofs"},
		{"mismatch", "theorem final : True := trivial\n", "must prove the declared law"},
		{"sorry transitively", "theorem unfinished : Laws.final := by sorry\ntheorem final : Laws.final := unfinished\n", "unapproved axiom sorryAx"},
		{"axiom", "axiom custom : Laws.final\ntheorem final : Laws.final := custom\n", "unapproved axiom"},
	} {
		t.Run(test.name, func(t *testing.T) {
			writeFile(t, docProofs, docHeader+test.body)
			checkLake(t, lake, dir, test.diagnostic, "doc_verify")
		})
	}
}

func TestScopedDirectiveDiagnostics(t *testing.T) {
	for _, test := range []struct{ name, source, diagnostic string }{
		{"invalid import", "//golean:verify:import a b\npackage sample\n", "input.go:1:1: expected //golean:verify:import"},
		{"misplaced import", "package sample\n//golean:assume:import a\nfunc f() {}\n", "input.go:2:1: //golean:assume:import belongs"},
		{"misplaced law", "package sample\n//golean:verify a : True\nvar x int\n", "input.go:2:1: //golean:verify requires"},
		{"duplicate law", "//golean:verify a : True\npackage sample\n//golean:verify a : True\ntype T int\n", "duplicate verification law"},
		{"duplicate between scopes", "package sample\n//golean:verify a : True\ntype T int\n//golean:verify a : True\nfunc F() {}\n", "duplicate verification law"},
		{"orphan continuation", "//golean:verify+ True\npackage sample\n", "input.go:1:1: expected a nonempty continuation"},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), test.source)
			_, err := transpile.Generate(dir)
			if err == nil || !strings.Contains(err.Error(), test.diagnostic) {
				t.Fatalf("wanted diagnostic %q, got %v", test.diagnostic, err)
			}
		})
	}
}
