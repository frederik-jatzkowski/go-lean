package main

import (
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func command(args ...string) error {
	cmd := newCommand()
	cmd.SetArgs(args)
	return cmd.Execute()
}

func put(t *testing.T, name, contents string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(name), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(name, []byte(contents), 0o644); err != nil {
		t.Fatal(err)
	}
}

func get(t *testing.T, name string) string {
	t.Helper()
	data, err := os.ReadFile(name)
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}

func missing(t *testing.T, name string) {
	t.Helper()
	if _, err := os.Stat(name); !os.IsNotExist(err) {
		t.Fatalf("%s: expected missing, got %v", name, err)
	}
}

func workspace(t *testing.T, leanPackage bool) {
	t.Helper()
	repo, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	repo = filepath.ToSlash(repo)
	t.Chdir(t.TempDir())
	t.Setenv("GOWORK", "off")
	mod := "module example.test/model\n\ngo 1.26.0\n"
	if leanPackage {
		mod += "\nrequire github.com/frederik-jatzkowski/go-lean v0.0.0\n" +
			"replace github.com/frederik-jatzkowski/go-lean => \"" + repo + "\"\n"
	}
	put(t, "go.mod", mod)
	if err := command("setup"); err != nil {
		t.Fatal(err)
	}
}

func TestPackageSelection(t *testing.T) {
	workspace(t, false)
	const source = `package client
import numbers "example.test/model/math"
//golean:verify law : Client 0 = 1
func Client(x int64) int64 { return numbers.Increment(x) }
func Ignored() { go func(){}() }
`
	put(t, "client/client.go", source)
	put(t, "math/math.go", `package math
//golean:export
func Increment(x int64) int64 { return helper(x) }
func helper(x int64) int64 { return x + 1 }
`)
	put(t, "client/nested/nested.go", "package nested\n//golean:export\nfunc Export() bool { return true }\n")
	put(t, "legacy/go.mod", "module example.test/legacy\n")
	put(t, "legacy/broken.go", "package this won't parse\n")
	// A manual root should survive both focused and workspace generation.
	put(t, "lakefile.toml", strings.Replace(get(t, "lakefile.toml"), "roots = [", "roots = [\n  'Manual',", 1))
	if err := command("transpile", "./client"); err != nil {
		t.Fatal(err)
	}
	missing(t, "client/nested/nested.lean")
	client := get(t, "client/client.lean")
	missing(t, "client/client_laws.lean")
	if !strings.Contains(client, "-- law :\n--   Client 0 = 1") ||
		strings.Index(client, "-- law :") > strings.Index(client, "import Std") ||
		!strings.Contains(client, "def «law» : Prop :=") {
		t.Fatal("model is missing the law review header or formal definition")
	}
	numbers := get(t, "math/math.lean")
	if !strings.Contains(client, "import «math».«math»") ||
		strings.Index(numbers, "def «helper»") > strings.Index(numbers, "def «Increment»") {
		t.Fatal("dependency was not generated and ordered")
	}
	proofFile := "client/client_proofs.lean"
	if !strings.HasPrefix(get(t, proofFile), "import «client».«client»\n") {
		t.Fatal("proof companion does not import the merged model")
	}
	if !strings.Contains(get(t, proofFile), "theorem «law» : Laws.«law»") {
		t.Fatal("missing scaffold")
	}
	const handwritten = "-- Handwritten proof companion.\r\n"
	put(t, proofFile, handwritten)
	if err := command("transpile", "./client/..."); err != nil {
		t.Fatal(err)
	}
	get(t, "client/nested/nested.lean")
	if err := command("transpile", "./..."); err != nil {
		t.Fatal(err)
	}
	lake := get(t, "lakefile.toml")
	if !strings.Contains(lake, "'Manual'") || strings.Contains(lake, "legacy") || get(t, proofFile) != handwritten {
		t.Fatal("generation changed a manual entry or proof, or selected an archived package")
	}
	if err := command("transpile", "./..."); err != nil {
		t.Fatal(err)
	}
	if get(t, "lakefile.toml") != lake || get(t, "client/client.lean") != client {
		t.Fatal("generation is not deterministic")
	}

	put(t, "client/client.go", strings.Replace(source, "return numbers.Increment(x)",
		"for x > 0 { x-- }; return numbers.Increment(x)", 1))
	err := command("transpile", "./...")
	if err == nil || !strings.Contains(err.Error(), "client.go:4:") || !strings.Contains(err.Error(), "unsupported statement") {
		t.Fatalf("expected source-located loop rejection, got %v", err)
	}
	if get(t, "client/client.lean") != client || get(t, "math/math.lean") != numbers || get(t, "lakefile.toml") != lake {
		t.Fatal("a subset error changed generated output")
	}
}

func TestSubsetDiagnostics(t *testing.T) {
	workspace(t, false)
	for _, tc := range []struct{ body, diagnostic string }{
		{"func F(x int64) int64 { return F(x) }", "recursive call"},
		{"func F(x int64) int64 { y := x; y = 1; return y }", "only immutable"},
		{"func F(x *[]int64) int64 { return 0 }", "unsupported type"},
		{"func F(x int64) int64 { return x * 2 }", "unsupported binary operator"},
		{"func F() bool { return len([1]int{}) == 1 }", "unsupported constant builtin call"},
	} {
		put(t, "f.go", "package example\n//golean:export\n"+tc.body+"\n")
		err := command("transpile", ".")
		if err == nil || !strings.Contains(err.Error(), tc.diagnostic) || !strings.Contains(err.Error(), "f.go:3:") {
			t.Errorf("%s: got %v, expected %q at a source position", tc.body, err, tc.diagnostic)
		}
	}
	missing(t, "example.lean")

	put(t, "f.go", "package example\n//golean:export\nfunc F() bool { return true }\n")
	const handwritten = "-- handwritten model at the new output path\n"
	put(t, "example.lean", handwritten)
	err := command("transpile", ".")
	if err == nil || !strings.Contains(err.Error(), "would overwrite a handwritten file") || get(t, "example.lean") != handwritten {
		t.Fatalf("expected the handwritten file to be preserved, got %v", err)
	}
}

func TestTargetWordSize(t *testing.T) {
	workspace(t, false)
	t.Setenv("GOOS", "linux")
	t.Setenv("GOARCH", "386")
	put(t, "word.go", "package word\n//golean:export\nfunc Next(x uint) uint { return x+1 }\n")
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	model := get(t, "word.lean")
	if !strings.Contains(model, "_root_.UInt32") || strings.Contains(model, "_root_.UInt64") {
		t.Fatalf("Go 386 word size did not reach the model:\n%s", model)
	}
}

func TestCuratedLeanSemantics(t *testing.T) {
	if _, err := exec.LookPath("lake"); err != nil {
		t.Skip("lake is unavailable")
	}
	workspace(t, true)
	put(t, "model.go", curatedGo)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	file := "model_proofs.lean"
	scaffold := get(t, file)
	// Exercise the axiom audit even with warning-as-error disabled.
	put(t, "lakefile.toml", strings.Replace(get(t, "lakefile.toml"), "-DwarningAsError=true", "-DwarningAsError=false", 1))
	cmd := exec.Command("lake", "build", "+model_verify")
	output, err := cmd.CombinedOutput()
	var failure *exec.ExitError
	if !errors.As(err, &failure) || !strings.Contains(string(output), "unapproved axiom sorryAx") {
		t.Fatalf("expected scaffold to fail axiom audit, got %v\n%s", err, output)
	}
	for _, law := range []string{"arrays", "bits", "bytes", "branches", "lists", "options", "ordered", "overflow", "signedMinimum"} {
		proof := "theorem «" + law + "» : Laws.«" + law + "» := by\n"
		scaffold = strings.Replace(scaffold, proof+"  sorry", proof+"  unfold Laws.«"+law+"»\n  decide", 1)
	}
	put(t, file, scaffold)
	output, err = exec.Command("lake", "build", "+model_verify").CombinedOutput()
	if err != nil {
		t.Fatalf("proof verification failed: %v\n%s", err, output)
	}
}

const curatedGo = `package model

import curated "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type key int16

//golean:export
func Bool() bool { return true }

//golean:verify branches : Branches true = 7 ∧ Branches false = 7
func Branches(choose bool) int8 {
	x := int8(7)
	if choose {
		var x = x - 1
		if x == 0 { return x }
	} else {
		var x = x + 1
		if x == 0 { return x }
	}
	return x
}

//golean:verify arrays : Arrays = true
func Arrays() bool {
	empty := curated.Array[int8]{}
	a := empty.Push(5).Push(7)
	b := a.Set(0, 9).Set(8, 11).Pop()
	return empty.Pop().Size() == 0 && b.Size() == 1 &&
		b.Get(0).UnwrapOr(0) == 9 && !b.Get(1).IsSome() && a.Get(0).UnwrapOr(0) == 5
}

//golean:verify bytes : Bytes = true
func Bytes() bool {
	a := curated.ByteArray{}.Push(5).Push(7).Push(9)
	b := a.Set(1, 8).Set(9, 12).Extract(1, 10)
	return b.Size() == 2 && b.Get(0).UnwrapOr(0) == 8 && b.Get(1).UnwrapOr(0) == 9 &&
		!b.Get(2).IsSome() && b.Extract(1, 0).Size() == 0 && b.Extract(5, 9).Size() == 0
}

//golean:verify ordered : Ordered = true
func Ordered() bool {
	m := curated.RBMap[string, int8]{}.Insert("\xff", 7).Insert("\x00", 1)
	r := m.Insert("\xff", 8).Erase("\x00")
	s := curated.RBSet[key]{}.Insert(-2).Insert(1).Insert(-2).Erase(1)
	return before("\x00", "\xff") && !before("\xff", "\x00") && m.Find("\xff").UnwrapOr(0) == 7 &&
		r.Find("\xff").UnwrapOr(0) == 8 && !r.Contains("\x00") &&
		s.Contains(-2) && !s.Contains(1)
}

func before(a, b string) bool { return a < b }

//golean:verify options : Options = true
func Options() bool {
	a := curated.None[int8]()
	b := curated.Option[int8]{}
	c := curated.Some(int8(0))
	return !a.IsSome() && !b.IsSome() && c.IsSome() &&
		a.UnwrapOr(9) == 9 && c.UnwrapOr(9) == 0
}

//golean:verify lists : Lists = true
func Lists() bool {
	a := curated.Nil[int8]()
	b := curated.List[int8]{}
	return a.IsEmpty() && b.IsEmpty() && !curated.Cons(int8(0), a).IsEmpty()
}

//golean:verify bits : Bits = true
func Bits() bool {
	empty := curated.BitVec{}
	zero := curated.NewBitVec(0, 7).UnwrapOr(empty)
	a := curated.NewBitVec(64, 1).UnwrapOr(empty)
	b := a.Set(63, true).Set(0, false).Set(64, true)
	return zero.Width() == 0 && zero.ToUint64() == 0 && !zero.Get(0).IsSome() &&
		a.Width() == 64 && a.Get(0).UnwrapOr(false) && b.Get(63).UnwrapOr(false) &&
		!b.Get(0).UnwrapOr(true) && !b.Get(64).IsSome() &&
		b.ToUint64() == 9223372036854775808 && !curated.NewBitVec(65, 0).IsSome()
}

//golean:verify overflow : Overflow 127 = -128
func Overflow(x int8) int8 { return x + 1 }

//golean:verify signedMinimum : SignedMinimum = true
func SignedMinimum() bool { return Overflow(127) == -128 }
`
