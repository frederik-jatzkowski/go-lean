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

func TestRejectMultiResultInterfaceContract(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample

//golean:assume law : True
type Service interface {
	Get() (int64, bool)
}

//golean:verify
func Read(s Service) int64 {
	n, _ := s.Get()
	return n
}
`)
	_, err := transpile.Generate(dir)
	if err == nil || !strings.Contains(err.Error(), "interface contract methods require at most one result") {
		t.Fatalf("expected a result-arity diagnostic, got %v", err)
	}
}

func TestImportedInterfaceContract(t *testing.T) {
	dir := newModule(t)
	source, err := format.Source([]byte(`package boundary

// Evaluator models a read.
//
//golean:assume read_identity : ∀ s x, Read s x = x
//golean:assume second_law : True
type Evaluator interface {
	//golean:assume read_zero : ∀ s, Read s 0 = 0
	Read(int) int
}

//golean:assume unused_law : True
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
	got := generatedFile(t, outputs, "sample_model.lean").Source
	for _, want := range []string{
		"import «boundary».«boundary_model»",
		"«example.test/sample/boundary».InterfaceContracts.«EvaluatorContract»",
		".«Read» «v0_e» «v1_x»",
		".«read» «contract:",
		": Option Int",
	} {
		if !strings.Contains(got, want) {
			t.Errorf("missing %q in output:\n%s", want, got)
		}
	}
	if strings.Contains(got, "\nstructure ") {
		t.Fatalf("caller redefined a contract:\n%s", got)
	}
	contract := generatedFile(t, outputs, "boundary_model.lean").Source
	if strings.Count(contract, "\nstructure ") != 1 || strings.Contains(contract, "unused_law") {
		t.Fatalf("expected only the reached contract:\n%s", contract)
	}
	previous := -1
	for _, law := range []string{"read_identity : ∀ s x, Read s x = x", "second_law : True", "read_zero : ∀ s, Read s 0 = 0"} {
		if index := strings.Index(contract, law); index <= previous {
			t.Fatalf("expected contract laws in declaration order:\n%s", contract)
		} else {
			previous = index
		}
	}
}

func TestInterfaceContractRejections(t *testing.T) {
	const contract = "//golean:assume valid : True\n"
	for _, test := range []struct {
		name, declaration, function, message string
	}{
		{"unannotated", "type Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator, x int64) int64 { return e.Evaluate(x) }", "requires a golean contract"},
		{"legacy start", "//golean:start\ntype Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator) int64 { return e.Evaluate(0) }", "use //golean:assume"},
		{"legacy end", "//golean:end\ntype Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator) int64 { return e.Evaluate(0) }", "use //golean:assume"},
		{"legacy law", "//golean:law valid : True\ntype Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator) int64 { return e.Evaluate(0) }", "use //golean:assume"},
		{"empty law", "//golean:assume\ntype Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator) int64 { return e.Evaluate(0) }", "expected //golean:assume"},
		{"missing law name", "//golean:assume : True\ntype Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator) int64 { return e.Evaluate(0) }", "expected //golean:assume"},
		{"missing proposition", "//golean:assume empty :\ntype Evaluator interface { Evaluate(int64) int64 }", "func Apply(e Evaluator) int64 { return e.Evaluate(0) }", "expected //golean:assume"},
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
	//golean:assume invalid_law : ∀ s, Evaluate s true = 0
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
