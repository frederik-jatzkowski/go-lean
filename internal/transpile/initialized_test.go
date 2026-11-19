package transpile_test

import (
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

const initializedRecord = `package sample

//golean:assume validReader : True
type Reader interface { Read(int64) int64 }

//golean:assume validGate : True
type Gate interface { Enabled() bool }

type Settings struct {
	//golean:assume:initialized
	left, right Reader
	//golean:assume:initialized
	gate Gate
	offset int64
}
`

func TestInitializedInterfaceFields(t *testing.T) {
	const source = initializedRecord + `
//golean:verify:constructor
func NewSettings(left, right Reader, gate Gate, swap bool) Settings {
	if swap {
		return Settings{left: right, right: left, gate: gate}
	}
	return Settings{left: left, right: right, gate: gate, offset: 3}
}

func read(reader Reader, offset int64) int64 { return reader.Read(offset) }

func evaluate(settings Settings) int64 {
	if settings.gate.Enabled() {
		return read(settings.left, settings.offset)
	}
	return read(settings.right, settings.offset)
}

//golean:verify
func (settings Settings) Evaluate() int64 { return evaluate(settings) }
`
	const proof = `
namespace GoLean.«example.test/sample».input

private def gate : InterfaceContracts.GateContract Bool :=
  ⟨id, trivial⟩
private def reader : InterfaceContracts.ReaderContract Bool :=
  ⟨fun left x => if left then x + 1 else x + 2, trivial⟩

example : «Settings$Evaluate» gate reader ⟨true, false, true, 10⟩ = 11 ∧
    «Settings$Evaluate» gate reader ⟨true, false, false, 10⟩ = 12 := by decide

end GoLean.«example.test/sample».input
`
	for _, constructor := range []bool{true, false} {
		name := "without_constructor_verification"
		input := strings.Replace(source, "//golean:verify:constructor\n", "", 1)
		if constructor {
			name = "with_constructor_verification"
			input = source
		}
		t.Run(name, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), input)
			outputs, err := transpile.Generate(dir)
			if err != nil {
				t.Fatal(err)
			}
			generated := outputs[0].Source
			for _, want := range []string{"«field:left»", "«field:right»", "«field:gate»", "«field:offset»", "«Settings$Evaluate»"} {
				if !strings.Contains(generated, want) {
					t.Errorf("missing %s in generated model", want)
				}
			}
			if strings.Contains(generated, "«NewSettings$initialized»") != constructor {
				t.Fatalf("constructor theorem presence should be %t", constructor)
			}
			checkInitializedLean(t, dir, outputs[0].Path, generated+proof)
		})
	}
}

func TestInitializedInterfaceFieldRejections(t *testing.T) {
	for _, tc := range []struct {
		name, function, diagnostic string
	}{
		{"missing field", "return Settings{left: left, gate: gate}", "initialize every interface field"},
		{"explicit nil", "return Settings{left: left, right: nil, gate: gate}", "initialize every interface field"},
		{"zero branch", "if swap { return Settings{} }; return Settings{left, right, gate, 0}", "constructor must"},
		{"nonparameter assignment", "local := left; if swap { local = right }; return Settings{local, right, gate, 0}", "initialize every interface field"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), initializedRecord+`
//golean:verify:constructor
func NewSettings(left, right Reader, gate Gate, swap bool) Settings { `+tc.function+" }\n")
			_, err := transpile.Generate(dir)
			if err == nil || !strings.Contains(err.Error(), tc.diagnostic) {
				t.Fatalf("expected %q, got %v", tc.diagnostic, err)
			}
		})
	}
	for _, tc := range []struct {
		name, source, diagnostic string
	}{
		{"unannotated", strings.Replace(initializedRecord, "//golean:assume:initialized\n", "", 1) + `
//golean:verify
func Evaluate(settings Settings) int64 { return settings.left.Read(0) }
`, "requires //golean:assume:initialized"},
		{"mutation", initializedRecord + `
//golean:verify
func (settings Settings) Evaluate(next Reader) int64 {
	settings.left = next
	return settings.left.Read(0)
}
`, "read-only local copy"},
		{"pointer receiver", initializedRecord + `
//golean:verify
func (settings *Settings) Evaluate() int64 { return settings.left.Read(0) }
`, "parameter must have a supported"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), tc.source)
			_, err := transpile.Generate(dir)
			if err == nil || !strings.Contains(err.Error(), tc.diagnostic) {
				t.Fatalf("expected %q, got %v", tc.diagnostic, err)
			}
		})
	}
}

func checkInitializedLean(t *testing.T, dir, path, source string) {
	t.Helper()
	lean, err := exec.LookPath("lean")
	if err != nil {
		t.Log("Lean is unavailable on PATH")
		return
	}
	writeFile(t, path, source)
	output, err := exec.Command(lean, "--root="+dir, path).CombinedOutput()
	if err != nil {
		t.Fatalf("Lean rejected generated model: %v\n%s", err, output)
	}
}
