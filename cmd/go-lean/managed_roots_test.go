package main

import (
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"

	"github.com/frederik-jatzkowski/go-lean/internal/lean"
)

const lakeBlock = "  # BEGIN go-lean managed roots\n  # END go-lean managed roots\n"

func TestManagedRootsReconcile(t *testing.T) {
	t.Chdir(t.TempDir())
	write(t, "go.mod", "module example.test/tree\n\ngo 1.26.0\n")
	const first = `name = "Example"
srcDir = "src"
defaultTargets = ["Proofs", "Nested"]

[[lean_lib]]
name = "Proofs"
roots = [
  "rules",
`
	const second = `]

[[lean_lib]]
name = "Nested"
srcDir = "nested"
roots = [
  "«sub»" # keep this formatting
]
`
	// The second block starts above a manual entry. The manual entry retains
	// its original whitespace, comment, and omission of a trailing comma.
	nested := strings.Replace(second, "  \"«sub»\"", lakeBlock+"  \"«sub»\"", 1)
	crlf := func(value string) string { return strings.ReplaceAll(value, "\n", "\r\n") }
	write(t, "lakefile.toml", crlf(first+lakeBlock+nested))
	const verified = "package mainpkg\n\n//golean:verify truth : True\nfunc A() int64 { return 1 }\n"
	const exported = "package mainpkg\n\n//golean:export\nfunc A() int64 { return 1 }\n"
	const imports = "//golean:verify:import rules\npackage mainpkg\n"
	write(t, "src/a.go", verified)
	write(t, "src/doc.go", imports)
	write(t, "src/rules.lean", "-- handwritten rules\n")
	write(t, "src/nested/sub.go", "package nested\n\n//golean:export\nfunc B() int64 { return 1 }\n")
	write(t, "src/nested/sub.lean", "-- handwritten root\n")
	write(t, "src/ignored.go", "//go:build ignore\n\npackage mainpkg\n")
	owned := lean.GeneratedHeader + "\r\n"
	protected := []string{
		"src/ignored_gen.lean", "src/.hidden/orphan_gen.lean",
		"src/vendor/orphan_gen.lean", "src/othermodule/orphan_gen.lean",
	}
	write(t, "src/othermodule/go.mod", "module example.test/other\n")
	for _, path := range protected {
		write(t, path, owned)
	}
	write(t, "src/handmade_gen.lean", lean.GeneratedHeader+" (example)\n")
	write(t, "src/orphan_verify.lean", owned)
	write(t, "src/orphan_model.lean", owned)
	transpileTree(t)
	assertMissing(t, "src/orphan_verify.lean", "src/orphan_model.lean")

	insert := func(block string, entries ...string) string {
		return strings.Replace(block, lakeBlock, "  # BEGIN go-lean managed roots\n  '"+
			strings.Join(entries, "',\n  '")+"',\n  # END go-lean managed roots\n", 1)
	}
	want := crlf(first + insert(lakeBlock, "a_gen", "a_laws", "a_proofs", "a_verify", "mainpkg_model") +
		insert(nested, "nested_model", "sub_gen"))
	if got := read(t, "lakefile.toml"); got != want {
		t.Fatalf("unexpected generated Lake config:\n%s", got)
	}
	assertMissing(t, "src/a_proofs.lean")
	stamp := time.Unix(1_000_000_000, 0)
	if err := os.Chtimes("lakefile.toml", stamp, stamp); err != nil {
		t.Fatal(err)
	}
	transpileTree(t)
	info, err := os.Stat("lakefile.toml")
	if err != nil || !info.ModTime().Equal(stamp) || read(t, "lakefile.toml") != want {
		t.Fatalf("second transpile rewrote the configuration: %v", err)
	}
	withManualModel := strings.Replace(want, "  'sub_gen',\r\n", "", 1)
	withManualModel = strings.Replace(withManualModel, "  \"«sub»\"", "  \"sub_gen\",\r\n  \"«sub»\"", 1)
	write(t, "lakefile.toml", strings.Replace(withManualModel, "  # END go-lean managed roots\r\n  \"sub_gen\"",
		"  'sub_gen',\r\n  # END go-lean managed roots\r\n  \"sub_gen\"", 1))
	transpileTree(t)
	if read(t, "lakefile.toml") != withManualModel {
		t.Fatal("managed roots duplicated a manual root")
	}
	write(t, "lakefile.toml", want)

	write(t, "src/a_proofs.lean", "-- user proof\n")
	write(t, "src/doc.go", "package mainpkg\n")
	transpileTree(t)
	assertMissing(t, "src/a_laws.lean")
	if strings.Contains(read(t, "lakefile.toml"), "'a_laws'") {
		t.Fatal("obsolete laws root survived regeneration")
	}
	write(t, "src/a.go", exported)
	transpileTree(t)
	assertMissing(t, "src/a_verify.lean")
	if config := read(t, "lakefile.toml"); strings.Contains(config, "'a_verify'") || strings.Contains(config, "'a_proofs'") {
		t.Fatal("obsolete verification or proof root survived regeneration")
	}
	write(t, "src/a.go", strings.Replace(exported, "//golean:export\n", "", 1))
	if err := os.Remove("src/nested/sub.go"); err != nil {
		t.Fatal(err)
	}
	transpileTree(t)
	assertMissing(t, "src/a_gen.lean", "src/mainpkg_model.lean", "src/nested/sub_gen.lean", "src/nested/nested_model.lean")
	if got := read(t, "lakefile.toml"); got != crlf(first+lakeBlock+nested) {
		t.Fatalf("unexpected config after directive removal and deletion:\n%s", got)
	}
	for _, path := range protected {
		if got := read(t, path); got != owned {
			t.Errorf("changed excluded file %s", path)
		}
	}
	if read(t, "src/a_proofs.lean") != "-- user proof\n" ||
		read(t, "src/handmade_gen.lean") != lean.GeneratedHeader+" (example)\n" {
		t.Fatal("changed a handwritten file")
	}
}

func TestManagedRootsLakeBuildAfterRename(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("Lake is unavailable on PATH")
	}
	toolchain := read(t, "../../lean-toolchain")
	t.Chdir(t.TempDir())
	write(t, "lean-toolchain", toolchain)
	write(t, "go.mod", "module example.test/tree\n\ngo 1.26.0\n")
	write(t, "lakefile.toml", "name = \"Example\"\ndefaultTargets = [\"Proofs\"]\n"+
		"[[lean_lib]]\nname = \"Proofs\"\nroots = [\n"+lakeBlock+"]\n")
	build := func(args ...string) {
		t.Helper()
		if output, err := exec.CommandContext(t.Context(), lake, append([]string{"build"}, args...)...).CombinedOutput(); err != nil {
			t.Fatalf("lake build %v: %v\n%s", args, err, output)
		}
	}
	writeProof := func(dir, module, stem string) {
		write(t, dir+"/"+stem+"_proofs.lean", "import "+module+"_gen\n"+
			"namespace GoLean.«example.test/tree/"+dir+"»."+stem+".Proofs\n"+
			"theorem truth : Laws.truth := True.intro\n")
	}
	write(t, "original/a.go", "package sample\n\n//golean:verify truth : True\nfunc A() int64 { return 1 }\n")
	writeProof("original", "original.a", "a")
	transpileTree(t)
	build()

	if err := os.Mkdir("renamed.part", 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.Rename("original/a.go", "renamed.part/b.go"); err != nil {
		t.Fatal(err)
	}
	if err := os.Remove("original/a_proofs.lean"); err != nil {
		t.Fatal(err)
	}
	writeProof("renamed.part", "«renamed.part».b", "b")
	transpileTree(t)
	assertMissing(t, "original/a_gen.lean", "original/a_verify.lean", "original/sample_model.lean")
	if config := read(t, "lakefile.toml"); strings.Contains(config, "original.") {
		t.Fatalf("old roots survived the rename:\n%s", config)
	}
	build()
	build("«renamed.part».b_verify")
}

func TestManagedRootsValidationBeforeWrites(t *testing.T) {
	const library = "[[lean_lib]]\nname = \"Proofs\"\n"
	for _, test := range []struct{ name, config, want string }{
		{"outside array", library + lakeBlock + "roots = []\n", "must be inside"},
		{"nested array", library + "roots = [[\n" + lakeBlock + "]]\n", "must be inside"},
		{"missing end", library + "roots = [\n  # BEGIN go-lean managed roots\n]\n", "missing END"},
		{"duplicate", library + "roots = [\n" + lakeBlock + lakeBlock + "]\n", "expected one BEGIN"},
		{"trailing comment", library + "roots = [\n \"rules\", # BEGIN go-lean managed roots\n # END go-lean managed roots\n]\n", "own lines"},
		{"explicit globs", library + "globs = []\nroots = [\n" + lakeBlock + "]\n", "explicit globs"},
		{"ambiguous", library + "roots = [\n" + lakeBlock + "]\n[[lean_lib]]\nname = \"Other\"\n", "share the managed source directory"},
		{"missing comma", library + "roots = [\n  \"rules\"\n" + lakeBlock + "]\n", "invalid TOML"},
		{"conflicting output", library + "roots = [\n" + lakeBlock + "]\n", "without the go-lean generated header"},
	} {
		t.Run(test.name, func(t *testing.T) {
			t.Chdir(t.TempDir())
			write(t, "go.mod", "module example.test/tree\n\ngo 1.26.0\n")
			write(t, "a.go", "package sample\n\n//golean:export\nfunc A() int64 { return 1 }\n")
			write(t, "lakefile.toml", test.config)
			old := lean.GeneratedHeader + "\n-- obsolete\n"
			write(t, "obsolete_gen.lean", old)
			if test.name == "conflicting output" {
				write(t, "a_gen.lean", "-- handwritten\n")
			}
			if err := run("transpile", "./..."); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("wanted %q, got %v", test.want, err)
			}
			if read(t, "lakefile.toml") != test.config || read(t, "obsolete_gen.lean") != old {
				t.Fatal("validation failure changed configuration or pruned a file")
			}
			if test.name == "conflicting output" {
				if read(t, "a_gen.lean") != "-- handwritten\n" {
					t.Fatal("overwrote a conflicting output")
				}
			} else {
				assertMissing(t, "a_gen.lean")
			}
		})
	}
}

func transpileTree(t *testing.T) {
	t.Helper()
	if err := run("transpile", "./..."); err != nil {
		t.Fatal(err)
	}
}

func assertMissing(t *testing.T, paths ...string) {
	t.Helper()
	for _, path := range paths {
		if _, err := os.Stat(path); !os.IsNotExist(err) {
			t.Errorf("expected %s to be absent, got %v", path, err)
		}
	}
}
