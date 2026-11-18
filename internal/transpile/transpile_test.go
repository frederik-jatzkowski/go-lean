package transpile_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func writeFile(t *testing.T, path, content string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
}

func newModule(t *testing.T) string {
	t.Helper()
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, "go.mod"), "module example.test/sample\n\ngo 1.27.0\n")
	return dir
}

func TestLowerSSA(t *testing.T) {
	path := filepath.Join(newModule(t), "input.go")
	writeFile(t, path, `package match
//golean:verify
func def(x int64) int64 {
	x = -x
	if x < 0 {
		x := -x
		if x == 0 {
			return -0x8000_0000_0000_0000
		}
		return x
	}
	return x
}
//golean:verify
func folded() int64 {
	return ((9223372036854775807 + 1) - 1) - (4 / 2)
}
`)
	outputs, err := transpile.Generate(filepath.Dir(path))
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	for _, want := range []string{
		"def «example.test/sample».«input».«def»",
		"(-«v0_x»)",
		"(Int64.ofInt (-9223372036854775808))",
		"(Int64.ofInt (9223372036854775805))",
	} {
		if !strings.Contains(got, want) {
			t.Errorf("missing %q in output:\n%s", want, got)
		}
	}
}

func TestRejectUnsupportedSSA(t *testing.T) {
	tests := []struct {
		name, source, want string
	}{
		{"remainder", "func f(x int64) int64 { return x % 2 }", "unsupported runtime operation %"},
		{"parameter", "func f(x int32) int64 { return 0 }", "parameter must have type int64"},
		{"result", "func f(x int64) float64 { return 1 }", "expected a top-level function with an int64 or bool result"},
		{"loop", "func f(x int64) int64 { for x > 0 { x = x - 1 }; return x }", "control-flow loops are unsupported"},
		{"join", "func f(x int64) int64 { if x < 0 { x = 0 }; return x }", "control-flow joins with non-bool values are unsupported"},
		{"global", "func f() int64 { return n }; var n int64", "unsupported unary operation *"},
		{"recursion", "func f(x int64) int64 { return f(x) }", "recursive calls are unsupported"},
		{"panic", "func f(x int64) int64 { panic(x) }", "unsupported SSA instruction"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			path := filepath.Join(newModule(t), "input.go")
			writeFile(t, path, "package sample\n//golean:verify\n"+test.source+"\n")
			_, err := transpile.Generate(filepath.Dir(path))
			if err == nil || !strings.Contains(err.Error(), path+":3:") || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("got %v, want a source position and %q", err, test.want)
			}
		})
	}
}

func TestTransitiveImportedCalls(t *testing.T) {
	dir := newModule(t)
	path := filepath.Join(dir, "input.go")
	writeFile(t, path, `package sample
import "example.test/sample/middle"
//golean:verify
func Root(x int64) int64 { return middle.Add(x) + middle.Add(x) }
`)
	writeFile(t, filepath.Join(dir, "middle", "middle.go"), `package middle
import "example.test/sample/leaf"
func Add(x int64) int64 { return leaf.Add(x) }
`)
	leaf := filepath.Join(dir, "leaf", "leaf.go")
	writeFile(t, leaf, "package leaf\nfunc Add(x int64) int64 { return x + 1 }\n")

	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	leafDef := "def «example.test/sample».«input».Dependencies.«example.test/sample/leaf».«Add»"
	middleDef := "def «example.test/sample».«input».Dependencies.«example.test/sample/middle».«Add»"
	rootDef := "def «example.test/sample».«input».«Root»"
	if strings.Count(got, leafDef) != 1 || strings.Count(got, middleDef) != 1 ||
		strings.Index(got, leafDef) >= strings.Index(got, middleDef) ||
		strings.Index(got, middleDef) >= strings.Index(got, rootDef) {
		t.Fatalf("expected one definition per function in dependency order:\n%s", got)
	}

	writeFile(t, leaf, "package leaf\nfunc Add(x int64) int64 { return x % 2 }\n")
	_, err = transpile.Generate(dir)
	for _, want := range []string{"call to example.test/sample/middle.Add", "call to example.test/sample/leaf.Add", "unsupported runtime operation %"} {
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("got %v, want %q in the call chain", err, want)
		}
	}
}
