package transpile_test

import (
	"go/format"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func TestImportedInterfaceContract(t *testing.T) {
	dir := newModule(t)
	source, err := format.Source([]byte(`package boundary

// Evaluator models a read.
//
// golean:start
// read_identity : ∀ s x, Read s x = x
// golean:end
type Evaluator interface {
	//golean:start
	// read_zero : ∀ s, Read s 0 = 0
	//golean:end
	Read(int) int
}

// golean:start
// unused_law : True
// golean:end
type Unused interface { Read(int) int }
`))
	if err != nil {
		t.Fatal(err)
	}
	writeFile(t, filepath.Join(dir, "boundary", "boundary.go"), string(source))
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
import "example.test/sample/boundary"

func read(e boundary.Evaluator, x int) int { return e.Read(x) }

//golean:verify
func Apply(e boundary.Evaluator, x int) int { return read(e, x) }

//golean:verify
func Divide(e boundary.Evaluator, x int) int { return x / read(e, x) }
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	if len(outputs) != 1 {
		t.Fatalf("got %d outputs, want 1", len(outputs))
	}
	got := outputs[0].Source
	for _, want := range []string{
		".Dependencies.«example.test/sample/boundary».InterfaceContracts.«EvaluatorContract»",
		"read_identity : ∀ s x, Read s x = x",
		"read_zero : ∀ s, Read s 0 = 0",
		".«Read» «v0_e» «v1_x»",
		".«read» «contract:",
		": Option Int",
	} {
		if !strings.Contains(got, want) {
			t.Errorf("missing %q in output:\n%s", want, got)
		}
	}
	if strings.Count(got, "\nstructure ") != 1 || strings.Contains(got, "unused_law") {
		t.Fatalf("expected only the reached contract:\n%s", got)
	}
}

func TestInterfaceContractRejections(t *testing.T) {
	const contract = "//golean:start\n// valid : True\n//golean:end\n"
	for _, test := range []struct {
		name, declaration, function, message string
	}{
		{"unannotated", "type Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator, x int64) int64 { return e.Evaluate(x) }", "requires a golean contract"},
		{"unclosed", "//golean:start\n// valid : True\ntype Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator) int64 { return e.Evaluate(0) }", "no matching golean:end"},
		{"nested", "//golean:start\n//golean:start\n//golean:end\ntype Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator) int64 { return e.Evaluate(0) }", "nested golean:start"},
		{"embedded", "type Reader interface { Evaluate(int64) int64 }\n" + contract + "type Evaluator interface { Reader }", "func Apply(e Evaluator) int64 { return e.Evaluate(0) }", "embedded interfaces"},
		{"nil receiver", contract + "type Evaluator interface { Evaluate(int64) int64 }", "func Apply() int64 { return Evaluator(nil).Evaluate(0) }", "non-nil handle"},
		{"nil comparison", contract + "type Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator) bool { return e == nil }", "unsupported runtime operation"},
		{"conversion", contract + "type Evaluator interface { Evaluate(int64) int64 }\ntype Concrete int64\nfunc (Concrete) Evaluate(x int64) int64 { return x }", "func Apply() Evaluator { return Concrete(0) }", "interface conversions"},
		{"assertion", contract + "type Evaluator interface { Evaluate(int64) int64 }\ntype Concrete int64\nfunc (Concrete) Evaluate(x int64) int64 { return x }", "func Apply(e Evaluator) Concrete { return e.(Concrete) }", "type assertions"},
		{"generic constraint", contract + "type Evaluator interface { Evaluate(int64) int64 }", "func Apply[T Evaluator](e T) int64 { return e.Evaluate(0) }", "unrestricted any constraint"},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), "package sample\n"+test.declaration+"\n//golean:verify\n"+test.function+"\n")
			_, err := transpile.Generate(dir)
			if err == nil || !strings.Contains(err.Error(), test.message) ||
				!regexp.MustCompile(`input\.go:\d+:\d+:`).MatchString(err.Error()) {
				t.Fatalf("want source-located %q, got %v", test.message, err)
			}
		})
	}
}

func TestIllTypedInterfaceLawRejectedByLean(t *testing.T) {
	lean, err := exec.LookPath("lean")
	if err != nil {
		t.Skip("Lean is unavailable on PATH")
	}
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
type Evaluator interface {
	//golean:start
	// invalid_law : ∀ s, Evaluate s true = 0
	//golean:end
	Evaluate(int64) int64
}

//golean:verify
func Apply(e Evaluator) int64 { return e.Evaluate(0) }
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	path := outputs[0].Path
	writeFile(t, path, outputs[0].Source)
	cmd := exec.Command(lean, "--root="+dir, path)
	result, err := cmd.CombinedOutput()
	if err == nil || !strings.Contains(string(result), "type mismatch") || !strings.Contains(string(result), "Bool") {
		t.Fatalf("expected Lean to reject the ill-typed law, got %v:\n%s", err, result)
	}
}
