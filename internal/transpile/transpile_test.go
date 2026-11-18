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

func TestMachineWordTargetWidth(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func roundTrip(x int) int { return int(uint(x)) }
`)
	t.Setenv("GOOS", "linux")
	for _, target := range []struct{ arch, width string }{{"386", "32"}, {"amd64", "64"}} {
		t.Run(target.arch, func(t *testing.T) {
			t.Setenv("GOARCH", target.arch)
			outputs, err := transpile.Generate(dir)
			if err != nil {
				t.Fatal(err)
			}
			got := outputs[0].Source
			for _, want := range []string{
				".GoTypes.Int := Int" + target.width,
				".GoTypes.UInt := UInt" + target.width,
				").toInt" + target.width,
				").toUInt" + target.width,
			} {
				if !strings.Contains(got, want) {
					t.Errorf("missing %q in output:\n%s", want, got)
				}
			}
		})
	}
}

func TestRejectUnsupportedSSA(t *testing.T) {
	tests := []struct {
		name, source, want string
	}{
		{"remainder", "func f(x int64) int64 { return x % 2 }", "unsupported runtime operation %"},
		{"parameter", "func f(x complex64) int64 { return 0 }", "parameter must have a supported scalar type"},
		{"result", "func f(x int64) complex64 { return 1 }", "expected a top-level function with one supported result"},
		{"dynamic any", "func f(x any) int64 { return 0 }", "parameter must have a supported scalar type"},
		{"constrained generic", "func f[T interface{ M() }](x T) T { return x }", "must use the unrestricted any constraint"},
		{"generic call", "func f(x int64) int64 { return id(x) }; func id[T any](x T) T { return x }", "calls to generic functions are unsupported"},
		{"closure writes capture", "func f(x int64) int64 { add := func() int64 { x++; return x }; return add() }", "closure captures may only be read"},
		{"parent writes capture", "func f(x int64) int64 { read := func() int64 { return x }; x++; return read() }", "unsupported local allocation or mutable capture"},
		{"closure initialization does not dominate", "func f(flag bool, x int64) int64 { var y int64; if flag { y = x }; read := func() int64 { return y }; return read() }", "unsupported local allocation or mutable capture"},
		{"closure escapes", "func f(x int64) int64 { saved = func() int64 { return x }; return x }; var saved func() int64", "closures may only be used in direct calls"},
		{"float32 multiply", "func f(x float32) float32 { return x * 2 }", "unsupported runtime operation *"},
		{"float64 addition", "func f(x float64) float64 { return x + 2 }", "unsupported runtime operation +"},
		{"loop", "func f(x int64) int64 { for x > 0 { x = x - 1 }; return x }", "control-flow loops are unsupported"},
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
