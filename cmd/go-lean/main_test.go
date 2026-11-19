package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func TestExamplesMatchGeneratedOutput(t *testing.T) {
	root, err := filepath.Abs(filepath.Join("..", ".."))
	if err != nil {
		t.Fatal(err)
	}
	outputs, err := transpile.Generate(root)
	if err != nil {
		t.Fatal(err)
	}
	found := make(map[string]bool, len(outputs))
	for _, output := range outputs {
		relative, err := filepath.Rel(root, output.Path)
		if err != nil {
			t.Fatal(err)
		}
		found[filepath.ToSlash(relative)] = true
		want := read(t, output.Path)
		if output.Source != want {
			t.Errorf("%s differs from transpiler output. Run make generate.", output.Path)
		}
	}
	for _, example := range []string{
		"acyclic_list", "arithmetic", "array_bounds", "batch_fulfillment", "boolean_implication", "bounded_counter", "branch_join", "byte_rune", "clamp", "clampimport", "constant_conversions",
		"division_guarded", "division_precondition", "division_propagation", "embedded_struct", "float32_rounding", "float64_special",
		"generic_identity", "generic_map", "immutable_closure", "integer_remainder", "machine_words", "map_build", "map_lookup", "movement_arrival", "multi_result", "narrow_signed", "nil_dereference", "range_fold",
		"slice_bounds", "slice_copy", "string_bytes", "struct_fields", "switch_tagless", "switch_value", "territory_methods", "unsigned_wrap",
	} {
		if !found["examples/provable/"+example+"/"+example+"_gen.lean"] {
			t.Errorf("missing generated module for %s", example)
		}
	}
	if !found["internal/subset/check_gen.lean"] {
		t.Error("missing generated module for subset.Binary")
	}
}

func TestTranspileTree(t *testing.T) {
	t.Chdir(t.TempDir())
	write(t, "go.mod", "module example.test/tree\n\ngo 1.27.0\n")
	write(t, "a.go", `package tree
//golean:verify
func A(x int64) int64 { return helper(x) }
func helper(x int64) int64 { return x + 1 }
`)
	write(t, "b.go", `package tree
//golean:verify
func B(x int64) int64 { return A(x) }
`)
	write(t, "nested/c.go", `package tree
//golean:verify
func C(x int64) int64 { return x }
`)
	write(t, "nested/unmarked.go", "package tree\nfunc Unmarked(x int64) int64 { return x % 2 }\n")
	write(t, "nested/skipped.go", "//go:build ignore\n\npackage tree\n//golean:verify\nfunc Skipped(x int64) int64 { return x }\n")

	if err := run("transpile", "./..."); err != nil {
		t.Fatal(err)
	}
	expected := map[string]string{
		"a_gen.lean":        "def «example.test/tree».«a».«A»",
		"b_gen.lean":        "def «example.test/tree».«b».«A»",
		"nested/c_gen.lean": "def «example.test/tree/nested».«c».«C»",
	}
	for file, definition := range expected {
		if got := read(t, file); !strings.Contains(got, definition) {
			t.Errorf("%s is missing %q:\n%s", file, definition, got)
		}
	}
	for _, path := range []string{"nested/unmarked_gen.lean", "nested/skipped_gen.lean"} {
		if _, err := os.Stat(path); !os.IsNotExist(err) {
			t.Errorf("expected no file at %s, got %v", path, err)
		}
	}
	if err := run("transpile", "a.go"); err == nil || !strings.Contains(err.Error(), "transpile ./...") {
		t.Fatalf("expected the tree command to be required, got %v", err)
	}

	original := read(t, "a_gen.lean")
	write(t, "a.go", strings.ReplaceAll(read(t, "a.go"), "x + 1", "x + 2"))
	write(t, "nested/c_gen.lean", "-- handwritten\n")
	if err := run("transpile", "./..."); err == nil || !strings.Contains(err.Error(), "generated header") {
		t.Fatalf("expected a conflicting output error, got %v", err)
	}
	if read(t, "a_gen.lean") != original || read(t, "nested/c_gen.lean") != "-- handwritten\n" {
		t.Fatal("a conflicting output changed a file")
	}
	write(t, "nested/c.go", strings.ReplaceAll(read(t, "nested/c.go"), "return x", "return x | 2"))
	if err := run("transpile", "./..."); err == nil || !strings.Contains(err.Error(), "unsupported runtime operation |") {
		t.Fatalf("expected a subset error, got %v", err)
	}
	if read(t, "a_gen.lean") != original {
		t.Fatal("failed subset validation changed a generated file")
	}
}

func run(args ...string) error {
	cmd := newCommand()
	cmd.SetArgs(args)
	return cmd.Execute()
}

func write(t *testing.T, path, content string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
}

func read(t *testing.T, path string) string {
	t.Helper()
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	return string(contents)
}
