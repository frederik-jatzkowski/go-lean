package transpile_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func TestTypeOnlyModelRemainsStableAcrossFocusedCallers(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "leaf", "leaf.go"), `package leaf
type Value struct { N int }
`)
	writeFile(t, filepath.Join(dir, "rename", "alias.go"), `package rename
import "example.test/sample/leaf"
type Value = leaf.Value
`)
	writeFile(t, filepath.Join(dir, "types", "records.go"), `package records
import "example.test/sample/rename"
type X struct { Value rename.Value }
type Y struct { N uint64 }
`)
	writeFile(t, filepath.Join(dir, "left", "caller.go"), `package left
import "example.test/sample/types"
//golean:verify
func Read(x records.X) int { return x.Value.N }
`)
	writeFile(t, filepath.Join(dir, "right", "caller.go"), `package right
import "example.test/sample/types"
//golean:verify
func Read(y records.Y) uint64 { return y.N }
`)
	writeFile(t, filepath.Join(dir, "lakefile.toml"), `name = "TypeOwners"
[[lean_lib]]
name = "TypeOwners"
roots = [
  # BEGIN go-lean managed roots
  # END go-lean managed roots
]
`)
	model := filepath.Join(dir, "types", "records_model.lean")
	var stable string
	for _, pattern := range []string{"./...", "./right", "./left"} {
		if _, err := transpile.ReconcilePattern(dir, pattern); err != nil {
			t.Fatal(err)
		}
		source, err := os.ReadFile(model)
		if err != nil {
			t.Fatal(err)
		}
		if stable == "" {
			stable = string(source)
			for _, want := range []string{"import «leaf».«leaf_model»", "structure «example.test/sample/types».«X»", "structure «example.test/sample/types».«Y»"} {
				if !strings.Contains(stable, want) {
					t.Fatalf("missing %s in package model:\n%s", want, stable)
				}
			}
		} else if stable != string(source) {
			t.Fatalf("generation with %s changed the canonical record model", pattern)
		}
	}
	if lake, err := exec.LookPath("lake"); err == nil {
		checkLake(t, lake, dir, "")
	}
}

func TestCrossPackageCollectionMismatchReportsGoCall(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "dep", "dep.go"), `package dep
//golean:export
func Len(xs []int64) int { return len(xs) }
`)
	caller := filepath.Join(dir, "input.go")
	writeFile(t, caller, `package sample
import "example.test/sample/dep"
//golean:verify
func Size(xs []int64) int {
	if xs == nil { return -1 }
	return dep.Len(xs)
}
`)
	_, err := transpile.Generate(dir)
	if err == nil || !strings.Contains(err.Error(), caller+":6:") || !strings.Contains(err.Error(), "different slice representation") {
		t.Fatalf("expected Go call-site diagnostic for incompatible slice representations, got %v", err)
	}
}
