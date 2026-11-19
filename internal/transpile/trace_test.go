package transpile_test

import (
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

const traceRepository = `
//golean:assume valid : True
type Repository interface {
	Read() int64
	Write(int64) int64
}
`

func TestVoidInterfaceEffectTrace(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample

//golean:assume valid : True
type Repository interface {
	Persist(int64)
}

//golean:boundary Repository.Persist effect
//golean:verify writes : True
func Save(repo Repository, approved bool) bool {
	if !approved {
		return false
	}
	repo.Persist(7)
	return true
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	source := outputs[0].Source
	for _, want := range []string{"→ Int64 → Unit", "example.test/sample.Repository.Persist"} {
		if !strings.Contains(source, want) {
			t.Errorf("generated model lacks %q", want)
		}
	}
	checkInitializedLean(t, dir, outputs[0].Path, source+`
namespace GoLean.«example.test/sample».input

private def repo : InterfaceContracts.RepositoryContract Unit :=
  ⟨fun _ _ => (), trivial⟩

example : Save repo () false = (false, []) := rfl
example : Save repo () true = (true, ["example.test/sample.Repository.Persist"]) := rfl

end GoLean.«example.test/sample».input
`)
}

func TestInterfaceEffectTraceIsolation(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "boundary", "repository.go"), "package boundary\n"+traceRepository)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
import "example.test/sample/boundary"

func helper(repo boundary.Repository, value int64) int64 { return repo.Write(value) }

//golean:boundary boundary.Repository.Write effect
//golean:verify writes : ∀ {H : Type}, H → True
func Save(repo boundary.Repository, value int64) int64 { return helper(repo, value) }

//golean:boundary boundary.Repository.Write readonly
//golean:verify reads : True
func Observe(repo boundary.Repository, value int64) int64 { return helper(repo, value) }

//golean:verify
func Legacy(repo boundary.Repository, value int64) int64 { return Save(repo, value) }
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	source := outputs[0].Source
	for _, want := range []string{"«Save$trace$0$helper»", "«Save$untraced»", "example.test/sample/boundary.Repository.Write"} {
		if !strings.Contains(source, want) {
			t.Errorf("generated model lacks %q", want)
		}
	}
	checkInitializedLean(t, dir, outputs[0].Path, source+`
namespace GoLean.«example.test/sample».input

private def repo : Dependencies.«example.test/sample/boundary».InterfaceContracts.RepositoryContract Unit :=
  ⟨fun _ => 0, fun _ value => value, trivial⟩

example : Save repo () 3 = (3, ["example.test/sample/boundary.Repository.Write"]) := rfl
example : Observe repo () 3 = (3, []) := rfl
example : Legacy repo () 3 = 3 := rfl

end GoLean.«example.test/sample».input
`)
}

func TestSequentialBoundaryEffects(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), "package sample\n"+traceRepository+`
//golean:assume valid : True
type Bus interface {
	Publish(int64)
}

func save(repo Repository, value int64) int64 {
	return repo.Write(value)
}

func publish(bus Bus, value int64, enabled bool) int64 {
	if enabled {
		bus.Publish(value)
	}
	return value
}

//golean:boundary Repository.Read readonly
//golean:boundary Repository.Write effect
//golean:boundary Bus.Publish effect
//golean:verify effects : True
func Run(repo Repository, bus Bus, enabled bool) int64 {
	value := repo.Read()
	value = repo.Write(value)
	value = save(repo, value)
	return publish(bus, value, enabled)
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	checkInitializedLean(t, dir, outputs[0].Path, outputs[0].Source+`
namespace GoLean.«example.test/sample».input

private def repo : InterfaceContracts.RepositoryContract Unit :=
  ⟨fun _ => 3, fun _ value => value + 1, trivial⟩

private def bus : InterfaceContracts.BusContract Unit :=
  ⟨fun _ _ => (), trivial⟩

example : Run bus repo () () true =
    (5, ["example.test/sample.Repository.Write", "example.test/sample.Repository.Write",
         "example.test/sample.Bus.Publish"]) := rfl
example : Run bus repo () () false =
    (5, ["example.test/sample.Repository.Write", "example.test/sample.Repository.Write"]) := rfl

end GoLean.«example.test/sample».input
`)
}

func TestRejectStrictInterfaceCalls(t *testing.T) {
	for _, tc := range []struct {
		name, entries, body, diagnostic string
	}{
		{"unlisted in helper", "Repository.Read readonly", "return write(repo, 0)", "Repository.Write is missing"},
		{"read after effect", "Repository.Write effect\n//golean:boundary Repository.Read readonly", "return write(repo, 0) + repo.Read()", "interface call after an effect"},
		{"read in helper after possible effect", "Repository.Write effect\n//golean:boundary Repository.Read readonly", "return maybeWrite(repo, repo.Read() > 0) + read(repo)", "call to read: readonly interface call after an effect"},
		{"duplicate", "Repository.Write effect\n//golean:boundary Repository.Write readonly", "return write(repo, 0)", "duplicate interface boundary"},
		{"unused", "Repository.Write effect\n//golean:boundary Repository.Read readonly", "return write(repo, 0)", "unused interface boundary"},
		{"invalid method", "Repository.Missing effect", "return write(repo, 0)", "expected a named interface method"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), "package sample\n"+traceRepository+`
func write(repo Repository, value int64) int64 { return repo.Write(value) }
func read(repo Repository) int64 { return repo.Read() }
func maybeWrite(repo Repository, enabled bool) int64 {
	if enabled { return write(repo, 0) }
	return 0
}

//golean:boundary `+tc.entries+`
//golean:verify law : True
func Run(repo Repository) int64 { `+tc.body+" }\n")
			_, err := transpile.Generate(dir)
			if err == nil || !strings.Contains(err.Error(), tc.diagnostic) {
				t.Fatalf("want %q, got %v", tc.diagnostic, err)
			}
		})
	}
}

func TestAllowedEffectBreaksEmptyTraceProof(t *testing.T) {
	lean, err := exec.LookPath("lean")
	if err != nil {
		t.Skip("Lean is unavailable on PATH")
	}
	for _, rejection := range []string{"return 0", "repo.Write(0); return 0"} {
		t.Run(rejection, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), "package sample\n"+traceRepository+`
//golean:boundary Repository.Write effect
//golean:verify reject : ∀ {H : Type} (repo : InterfaceContracts.RepositoryContract H) (handle : H),
//golean:verify+   Run repo handle false = (0, [])
func Run(repo Repository, approved bool) int64 {
	if !approved { `+rejection+` }
	return repo.Write(1)
}
`)
			outputs, err := transpile.Generate(dir)
			if err != nil {
				t.Fatal(err)
			}
			path := outputs[0].Path
			writeFile(t, path, outputs[0].Source+`
namespace GoLean.«example.test/sample».input
theorem reject : Laws.reject := by
  intro H repo handle
  rfl
end GoLean.«example.test/sample».input
`)
			out, err := exec.Command(lean, "--root="+dir, path).CombinedOutput()
			if rejection == "return 0" && err != nil {
				t.Fatalf("expected the proof to check: %v\n%s", err, out)
			}
			if rejection != "return 0" && (err == nil || !strings.Contains(string(out), "definitionally equal")) {
				t.Fatalf("expected the unexpected write to break the proof: %v\n%s", err, out)
			}
		})
	}
}
