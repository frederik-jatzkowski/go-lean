package transpile_test

import (
	"go/format"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func TestVerificationDirectiveDiagnostics(t *testing.T) {
	for _, test := range []struct {
		name, comments, diagnostic string
	}{
		{"malformed", "//golean:verify law True\n", "input.go:2:1: expected //golean:verify"},
		{"orphan", "//golean:verify+ True\n", "input.go:2:1: expected a nonempty continuation"},
		{"duplicate", "//golean:verify law : True\n//golean:verify law : True\n", "input.go:3:1: duplicate verification law"},
		{"unknown target", "//golean:abstract missing.Min\n", "input.go:2:1: expected //golean:abstract"},
		{"malformed assumption", "//golean:assume fact :\n", "input.go:2:1: expected //golean:assume"},
		{"duplicate assumption", "//golean:assume fact : True\n//golean:assume fact : True\n", "input.go:3:1: duplicate assumed law"},
		{"wrong continuation", "//golean:verify fact : True\n//golean:assume+ True\n", "input.go:3:1: expected a nonempty continuation"},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), "package sample\n"+test.comments+"func F() int64 { return 1 }\n")
			_, err := transpile.Generate(dir)
			if err == nil || !strings.Contains(err.Error(), test.diagnostic) {
				t.Fatalf("wanted %q, got %v", test.diagnostic, err)
			}
		})
	}
}

func TestAssumedBoundaryExamples(t *testing.T) {
	for _, test := range []struct {
		name, assumptions, law, weakened, callee string
	}{
		{"assumed_quota", "assumed_quota.go", "ReadQuota ≤ 10", "True", "ReadQuota"},
		{"assumed_worker", "worker/worker.go", "//golean:assume preservesInput : ∀ x : Int64,\n//golean:assume+ Mirror x = x", "//golean:assume preservesInput : True", "Mirror"},
		{"assumed_reflection", "assumed_reflection.go", "∀ r : Int64, Value r = r", "True", "Value"},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := t.TempDir()
			module, err := os.ReadFile(filepath.Join("..", "..", "go.mod"))
			if err != nil {
				t.Fatal(err)
			}
			writeFile(t, filepath.Join(dir, "go.mod"), string(module))
			stem := "examples/provable/" + test.name + "/" + test.name
			copyExample := func(path string) string {
				t.Helper()
				source, err := os.ReadFile(filepath.Join("..", "..", path))
				if err != nil {
					t.Fatal(err)
				}
				writeFile(t, filepath.Join(dir, path), string(source))
				return string(source)
			}
			source := copyExample(stem + ".go")
			assumptions := "examples/provable/" + test.name + "/" + test.assumptions
			laws := source
			if assumptions != stem+".go" {
				laws = copyExample(assumptions)
			}
			copyExample(stem + "_proofs.lean")
			moduleName := test.name + "." + test.name
			writeFile(t, filepath.Join(dir, "lakefile.toml"), `name = "Boundary"
defaultTargets = ["Boundary"]
moreLeanArgs = ["-DwarningAsError=true"]
[[lean_lib]]
name = "Boundary"
srcDir = "examples/provable"
roots = ["`+moduleName+`_model", "`+moduleName+`_gen", "`+moduleName+`_proofs", "`+moduleName+`_verify"]
`)
			outputs, err := transpile.Generate(dir)
			if err != nil {
				t.Fatal(err)
			}
			modelOutput := generatedFile(t, outputs, test.name+"_model.lean").Source
			verifyOutput := generatedFile(t, outputs, test.name+"_verify.lean").Source
			if !strings.Contains(modelOutput, ".operation") ||
				strings.Contains(verifyOutput, ".Linked.") || strings.Contains(modelOutput, "\naxiom ") ||
				strings.Contains(verifyOutput, "\naxiom ") {
				t.Fatalf("expected a conditional model and check for %s", stem)
			}
			model := filepath.Join(dir, stem+".go")
			for _, line := range strings.SplitAfter(source, "\n") {
				if strings.HasPrefix(line, "//golean:abstract ") {
					writeFile(t, model, strings.Replace(source, line, "", 1))
					break
				}
			}
			if _, err := transpile.Generate(dir); err == nil || !strings.Contains(err.Error(), "call to ") || !strings.Contains(err.Error(), test.callee) {
				t.Fatalf("expected rejection of ordinary call to %s, got %v", test.callee, err)
			}
			writeFile(t, model, source)
			t.Run("Lean", func(t *testing.T) {
				lake, err := exec.LookPath("lake")
				if err != nil {
					t.Skip("Lake is unavailable on PATH")
				}
				generateFiles(t, dir)
				checkLake(t, lake, dir, "")
				laws = strings.ReplaceAll(laws, "\r\n", "\n")
				if !strings.Contains(laws, test.law) {
					t.Fatalf("missing assumed law %q", test.law)
				}
				writeFile(t, filepath.Join(dir, assumptions), strings.Replace(laws, test.law, test.weakened, 1))
				generateFiles(t, dir)
				checkLake(t, lake, dir, test.name+"_proofs.lean")
			})
		})
	}
}

func TestAssumedMethodIdentity(t *testing.T) {
	dir := newModule(t)
	boundary := filepath.Join(dir, "boundary", "reading.go")
	const imported = `package boundary
type Remote int64
var reading int64
//golean:assume identity : ∀ r : Int64, Value r = r
func (r Remote) Value() int64 { return reading }
`
	writeFile(t, boundary, imported)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
import dep "example.test/sample/boundary"
type Local int64
var reading int64
//golean:assume identity : ∀ r : Int64, Value r = r
func (r Local) Value() int64 { return reading }
//golean:abstract Local.Value
//golean:abstract dep.Remote.Value
//golean:verify law : True
func Sum(x Local, y dep.Remote) int64 { return x.Value() + y.Value() }
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	model := generatedFile(t, outputs, "sample_model.lean").Source
	if !strings.Contains(model, "«contract:Local$Value».operation") ||
		!strings.Contains(model, "«contract:Remote$Value».operation") {
		t.Fatal("expected separate contracts for methods with the same name")
	}
	writeFile(t, boundary, strings.Replace(imported, "func (r Remote)", "//golean:verify\nfunc (r Remote)", 1))
	if _, err := transpile.Generate(dir); err == nil || !strings.Contains(err.Error(), "unsupported unary operation") {
		t.Fatalf("expected subset rejection when the assumed method is independently selected, got %v", err)
	}
}

func TestAbstractTargetDiagnostics(t *testing.T) {
	const source = `package sample
type Reading int64
//golean:assume a : True
func (*Reading) Value() int64 { return 0 }
//golean:assume a : True
func Unused() int64 { return 0 }
`
	for _, test := range []struct {
		target, diagnostic string
	}{
		{"Reading.Value", "methods require a scalar value receiver"},
		{"Unused", "must be called directly"},
		{"Reading.Missing", "expected //golean:abstract"},
	} {
		t.Run(test.target, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), source+"//golean:abstract "+test.target+"\n//golean:verify law : True\nfunc Caller(x Reading) int64 { return x.Value() }\n")
			_, err := transpile.Generate(dir)
			if err == nil || !strings.Contains(err.Error(), test.diagnostic) {
				t.Fatalf("wanted %q, got %v", test.diagnostic, err)
			}
		})
	}
}

func TestLakeEnforcesVerificationLaws(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("Lake is unavailable on PATH")
	}
	dir := newModule(t)
	input := filepath.Join(dir, "input.go")
	proofs := filepath.Join(dir, "input_proofs.lean")
	const source = `package sample
// F returns one.
//golean:verify correct : F = 1 ∧
//golean:verify+ True
//golean:verify another : F = F
func F() int64 { return 1 }
`
	formatted, err := format.Source([]byte(source))
	if err != nil {
		t.Fatal(err)
	}
	writeFile(t, filepath.Join(dir, "lakefile.toml"), `name = "Verification"
defaultTargets = ["Verification"]
moreLeanArgs = ["-DwarningAsError=true"]
[[lean_lib]]
name = "Verification"
roots = ["sample_model", "input_gen", "input_proofs", "input_verify"]
`)
	writeFile(t, input, string(formatted))
	generateFiles(t, dir)
	const header = "import input_gen\nnamespace GoLean.«example.test/sample».input.Proofs\n"
	const other = "theorem another : Laws.another := rfl\n"
	const original = "theorem correct : F = 1 ∧ True := ⟨rfl, trivial⟩\n"
	writeProofs := func(body string) { writeFile(t, proofs, header+other+body) }
	t.Run("missing companion", func(t *testing.T) {
		checkLake(t, lake, dir, "input_proofs.lean")
	})
	for _, test := range []struct{ name, proof, diagnostic string }{
		{"valid", original, ""},
		{"missing theorem", "", "must be declared in input_proofs"},
		{"wrong proposition", "theorem correct : True := trivial\n", "must prove the declared law"},
		{"sorry", "set_option warningAsError false in\ntheorem correct : Laws.correct := by sorry\n", "unapproved axiom sorryAx"},
		{"transitive axiom", "axiom custom : Laws.correct\ntheorem helper : Laws.correct := custom\ntheorem correct : Laws.correct := helper\n", "unapproved axiom GoLean.«example.test/sample».input.Proofs.custom"},
	} {
		t.Run(test.name, func(t *testing.T) {
			writeProofs(test.proof)
			checkLake(t, lake, dir, test.diagnostic)
		})
	}
	t.Run("changed law", func(t *testing.T) {
		writeProofs(original)
		writeFile(t, input, strings.Replace(string(formatted), "F = 1", "F = 2", 1))
		generateFiles(t, dir)
		checkLake(t, lake, dir, "must prove the declared law")
	})
	t.Run("trailing command in a proposition", func(t *testing.T) {
		writeFile(t, input, strings.Replace(string(formatted), "verify+ True", "verify+ True\n//golean:verify+ axiom injected : False", 1))
		generateFiles(t, dir)
		checkLake(t, lake, dir, "input.go:")
	})
}

func TestClampImportContracts(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("Lake is unavailable on PATH")
	}
	dir := t.TempDir()
	const clampPath = "examples/provable/clampimport"
	repo := filepath.Join("..", "..")
	for _, path := range []string{"go.mod", clampPath + "/clampimport.go", clampPath + "/clampimport_proofs.lean", clampPath + "/limits/limits.go", clampPath + "/limits/limits_proofs.lean"} {
		data, err := os.ReadFile(filepath.Join(repo, path))
		if err != nil {
			t.Fatal(err)
		}
		writeFile(t, filepath.Join(dir, path), string(data))
	}
	writeFile(t, filepath.Join(dir, "lakefile.toml"), `name = "Verification"
defaultTargets = ["Verification"]
moreLeanArgs = ["-DwarningAsError=true"]
srcDir = "examples"
[[lean_lib]]
name = "Verification"
srcDir = "provable"
roots = [
  "clampimport.clampimport_gen", "clampimport.clampimport_proofs", "clampimport.clampimport_verify",
  "clampimport.clampimport_model", "clampimport.limits.limits_model",
  "clampimport.limits.limits_gen", "clampimport.limits.limits_proofs", "clampimport.limits.limits_verify",
]
`)
	generateFiles(t, dir)
	model, err := os.ReadFile(filepath.Join(dir, clampPath, "clampimport_model.lean"))
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(string(model), ".Dependencies.") || strings.Contains(string(model), "import clampimport.limits") {
		t.Fatal("caller model depends on the concrete callee model")
	}
	checkLake(t, lake, dir, "", "clampimport.clampimport_proofs")
	calleeOlean := filepath.Join(dir, ".lake", "build", "lib", "lean", "clampimport", "limits", "limits_gen.olean")
	if _, err := os.Stat(calleeOlean); !os.IsNotExist(err) {
		t.Fatalf("abstract caller proof should build without the concrete callee model, stat returned %v", err)
	}
	checkLake(t, lake, dir, "")

	limits := filepath.Join(dir, clampPath, "limits", "limits.go")
	original, err := os.ReadFile(limits)
	if err != nil {
		t.Fatal(err)
	}
	t.Run("weakened contract", func(t *testing.T) {
		writeFile(t, limits, strings.Replace(string(original), "∀ x y : Int64, y ≤ x → Min x y = y", "True", 1))
		generateFiles(t, dir)
		checkLake(t, lake, dir, "minSpec.rightIdentity", "clampimport.clampimport_proofs")
	})
	t.Run("broken callee", func(t *testing.T) {
		writeFile(t, limits, strings.Replace(string(original), "return x", "return y", 1))
		generateFiles(t, dir)
		checkLake(t, lake, dir, "limits_proofs.lean", "clampimport.limits.limits_verify")
	})
}

func generateFiles(t *testing.T, dir string) {
	t.Helper()
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	if err := transpile.Write(outputs); err != nil {
		t.Fatal(err)
	}
}

func checkLake(t *testing.T, lake, dir, diagnostic string, targets ...string) {
	t.Helper()
	cmd := exec.CommandContext(t.Context(), lake, append([]string{"build"}, targets...)...)
	cmd.Dir = dir
	output, err := cmd.CombinedOutput()
	if diagnostic == "" && err != nil || diagnostic != "" && (err == nil || !strings.Contains(string(output), diagnostic)) {
		t.Fatalf("wanted Lake result %q, got %v:\n%s", diagnostic, err, output)
	}
}
