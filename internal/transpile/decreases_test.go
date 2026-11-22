package transpile_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func TestGuardedRecursion(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "lakefile.toml"), decreasesLake)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample

type Node struct { Left, Right []uint16 }

//golean:export
//golean:verify countZero : ∀ acc, Count 0 acc = some acc
//golean:decreases n.toNat
func Count(n uint16, acc uint16) uint16 {
	if n == 0 { return acc }
	return Count(n-1, acc+1)
}

//golean:export
//golean:decreases n.toNat
func Visit(t Node, n uint16, acc uint16) uint16 {
	if n == 0 || int(n) >= len(t.Left) || int(n) >= len(t.Right) { return acc }
	l, r := t.Left[n], t.Right[n]
	if l >= n || r >= n { return acc }
	after := Visit(t, l, acc+1)
	return Visit(t, r, after)
}
`)
	writeFile(t, filepath.Join(dir, "input_proofs.lean"), `import input_gen

open GoLean.«example.test/sample»
namespace GoLean.«example.test/sample».input.Proofs

theorem countZero : Laws.countZero := by
  intro acc
  rw [GoLean.«example.test/sample».Count.eq_def]
  simp

end GoLean.«example.test/sample».input.Proofs
`)
	targets, err := transpile.ReconcilePattern(dir, ".")
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(dir, "sample_decreases.lean")); !os.IsNotExist(err) {
		t.Fatalf("automatic proofs should not generate a separate decreases module: %v", err)
	}
	decreases, err := os.ReadFile(filepath.Join(dir, "sample_model.lean"))
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"Count$decrease1", "Visit$decrease1", "Visit$decrease2"} {
		if !strings.Contains(string(decreases), name) {
			t.Fatalf("missing obligation %s:\n%s", name, decreases)
		}
	}
	if lake, err := exec.LookPath("lake"); err == nil {
		checkLake(t, lake, dir, "", targets...)
	}
}

func TestCompanionDecreaseProof(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("Lake is unavailable on PATH")
	}
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "lakefile.toml"), decreasesLake)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample

//golean:export
//golean:decreases n.toNat * n.toNat
func Count(n uint16) uint16 {
	if n == 0 { return n }
	return Count(n-1)
}
`)
	build := func(diagnostic string) {
		t.Helper()
		targets, err := transpile.ReconcilePattern(dir, ".")
		if err != nil {
			t.Fatal(err)
		}
		checkLake(t, lake, dir, diagnostic, targets...)
	}
	build("input.go:7:")
	path := filepath.Join(dir, "sample_decreases_proofs.lean")
	const header = `import sample_decreases
namespace GoLean.«example.test/sample».Decreases
`
	const footer = "\nend GoLean.«example.test/sample».Decreases\n"
	writeFile(t, path, header+`theorem «Count$decrease1» : «Count$decrease1» := by
  unfold GoLean.«example.test/sample».«Count$decrease1»
  intros
  apply Nat.mul_self_lt_mul_self
  simp_all (config := { zetaDelta := true }) [«Count$measure», ← UInt16.toNat_inj, UInt16.toNat_sub] <;> omega
`+footer)
	build("")
	writeFile(t, path, header+`axiom trustMe : GoLean.«example.test/sample».«Count$decrease1»
theorem «Count$decrease1» : GoLean.«example.test/sample».«Count$decrease1» := trustMe
`+footer)
	build("depends on unapproved axiom")
	writeFile(t, path, header+`theorem «Count$decrease1» : GoLean.«example.test/sample».«Count$decrease1» := by sorry
`+footer)
	build("depends on unapproved axiom sorryAx")
	if err := os.Remove(path); err != nil {
		t.Fatal(err)
	}
	if _, err := transpile.ReconcilePattern(dir, "."); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(dir, "sample_decreases.lean")); !os.IsNotExist(err) {
		t.Fatalf("removing the companion should remove its generated module: %v", err)
	}
	lakefile, err := os.ReadFile(filepath.Join(dir, "lakefile.toml"))
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(string(lakefile), "sample_decreases") {
		t.Fatalf("removed decreases modules remain in managed roots:\n%s", lakefile)
	}
}

func TestRejectNonDecreasingCall(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("Lake is unavailable on PATH")
	}
	for _, call := range []string{"Again(n)", "Again(n-1)"} {
		t.Run(call, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "lakefile.toml"), decreasesLake)
			writeFile(t, filepath.Join(dir, "input.go"), `package sample

//golean:export
//golean:decreases n.toNat
func Again(n uint16) uint16 { return `+call+` }
`)
			targets, err := transpile.ReconcilePattern(dir, ".")
			if err != nil {
				t.Fatal(err)
			}
			checkLake(t, lake, dir, "could not prove Again$decrease1 for the Go call at", targets...)
		})
	}
}

const decreasesLake = `name = "Recursive"
[[lean_lib]]
name = "Recursive"
roots = [
  # BEGIN go-lean managed roots
  # END go-lean managed roots
]
`
