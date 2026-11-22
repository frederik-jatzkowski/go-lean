package main

import (
	"bytes"
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

func TestSetupAndDoctor(t *testing.T) {
	t.Chdir(t.TempDir())
	if err := run("setup"); err == nil {
		t.Fatal("setup accepted a directory without go.mod")
	}
	requireMissing(t, "lean-toolchain")
	write(t, "go.mod", "module example.test/workspace\n\ngo 1.26.0\n")
	write(t, "lakefile.lean", "import Lake\n")
	write(t, "lean-toolchain", "existing/toolchain:stable\n")

	t.Setenv("PATH", t.TempDir())
	var stderr bytes.Buffer
	cmd := newCommand()
	cmd.SetErr(&stderr)
	cmd.SetArgs([]string{"doctor"})
	if err := cmd.Execute(); !errors.Is(err, errDoctorFailed) {
		t.Fatalf("doctor returned %v", err)
	}
	for _, want := range []string{skillPath, "go is unavailable", "lake is unavailable", "lean is unavailable"} {
		if !strings.Contains(stderr.String(), want) {
			t.Errorf("doctor omitted %q from %s", want, stderr.String())
		}
	}
	requireMissing(t, skillPath)
	if err := run("doctor", "--fix"); !errors.Is(err, errDoctorFailed) {
		t.Fatalf("doctor --fix returned %v despite missing tools", err)
	}
	if !strings.Contains(read(t, skillPath), "go-lean verify") {
		t.Fatal("doctor --fix did not install the go-lean skill")
	}
	requireMissing(t, "lakefile.toml")

	write(t, skillPath, "custom skill\n")
	if err := run("setup"); err != nil {
		t.Fatal(err)
	}
	for path, want := range map[string]string{
		"lean-toolchain": "existing/toolchain:stable\n",
		"lakefile.lean":  "import Lake\n",
		skillPath:        "custom skill\n",
	} {
		if got := read(t, path); got != want {
			t.Errorf("%s changed to %q", path, got)
		}
	}

	if err := os.Remove("lakefile.lean"); err != nil {
		t.Fatal(err)
	}
	const malformed = "[[lean_lib]]\nroots = [\n"
	write(t, "lakefile.toml", malformed)
	stderr.Reset()
	cmd = newCommand()
	cmd.SetErr(&stderr)
	cmd.SetArgs([]string{"doctor", "--fix"})
	if err := cmd.Execute(); !errors.Is(err, errDoctorFailed) || !strings.Contains(stderr.String(), "lakefile.toml:") {
		t.Fatalf("doctor --fix returned %v and reported %q for malformed TOML", err, &stderr)
	}
	if got := read(t, "lakefile.toml"); got != malformed {
		t.Fatal("doctor --fix overwrote malformed TOML")
	}
}

func TestFocusedTranspilePreservesOtherPackages(t *testing.T) {
	t.Chdir(t.TempDir())
	write(t, "go.mod", "module example.test/workspace\n\ngo 1.26.0\n")
	if err := run("setup"); err != nil {
		t.Fatal(err)
	}
	for _, dir := range []string{"one", "one/nested", "two"} {
		write(t, dir+"/model.go", "package model\n//golean:export\nfunc Model(x int64) int64 { return x }\n")
	}
	if err := run("transpile", "./one"); err != nil {
		t.Fatal(err)
	}
	read(t, "one/model_gen.lean")
	requireMissing(t, "one/nested/model_gen.lean")
	requireMissing(t, "two/model_gen.lean")
	if err := run("transpile", "./..."); err != nil {
		t.Fatal(err)
	}
	other := read(t, "two/model_gen.lean")
	write(t, "two/model.go", "package broken!\n")
	write(t, "one/model.go", "package model\n")
	if err := run("transpile", "./one/..."); err != nil {
		t.Fatal(err)
	}
	requireMissing(t, "one/model_gen.lean")
	if got := read(t, "two/model_gen.lean"); got != other {
		t.Fatal("focused transpilation modified an unrelated model")
	}
	roots := read(t, "lakefile.toml")
	for _, name := range []string{"one.nested.model_gen", "two.model_gen"} {
		if !strings.Contains(roots, name) {
			t.Errorf("focused transpilation removed %s", name)
		}
	}
	if strings.Contains(roots, "one.model_gen") {
		t.Fatal("focused transpilation left a stale root in the selected package")
	}
}

func TestVerifyRunsLakeAfterGeneration(t *testing.T) {
	t.Chdir(t.TempDir())
	write(t, "go.mod", "module example.test/workspace\n\ngo 1.26.0\n")
	write(t, "pkg/model.go", "package model\n//golean:export\nfunc Model(x int64) int64 { return x }\n")
	if err := run("setup"); err != nil {
		t.Fatal(err)
	}
	bin := t.TempDir()
	lake := filepath.Join(bin, "lake")
	if runtime.GOOS == "windows" {
		lake += ".exe"
	}
	source := filepath.Join(bin, "fake.go")
	write(t, source, `package main
import ("fmt"; "os"; "strings")
func main() {
	for _, path := range []string{"pkg/model_gen.lean", "pkg/model_model.lean"} {
		if _, err := os.Stat(path); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
	}
	fmt.Println(strings.Join(os.Args[1:], " "))
	fmt.Fprintln(os.Stderr, "from Lake")
	os.Exit(23)
}
`)
	if output, err := exec.Command("go", "build", "-o", lake, source).CombinedOutput(); err != nil {
		t.Fatalf("build fake Lake: %v\n%s", err, output)
	}
	t.Setenv("PATH", bin+string(os.PathListSeparator)+os.Getenv("PATH"))
	for _, tc := range []struct {
		args []string
		want string
	}{
		{[]string{"verify", "./pkg"}, "build +pkg.model_gen"},
		{[]string{"verify"}, "build"},
	} {
		var stdout, stderr bytes.Buffer
		cmd := newCommand()
		cmd.SetOut(&stdout)
		cmd.SetErr(&stderr)
		cmd.SetArgs(tc.args)
		err := cmd.Execute()
		var code *exec.ExitError
		if !errors.As(err, &code) || code.ExitCode() != 23 {
			t.Fatalf("%v returned %v", tc.args, err)
		}
		if strings.TrimSpace(stdout.String()) != tc.want || strings.TrimSpace(stderr.String()) != "from Lake" {
			t.Fatalf("%v emitted stdout %q and stderr %q", tc.args, &stdout, &stderr)
		}
	}
	write(t, "pkg/model.go", "package model\n")
	if err := run("verify", "./pkg"); err != nil {
		t.Fatalf("verify launched Lake without targets: %v", err)
	}
	write(t, "pkg/model.go", "package broken!\n")
	if err := run("verify", "./pkg"); err == nil || strings.Contains(err.Error(), "exit status 23") {
		t.Fatalf("verify failed to stop after transpilation error: %v", err)
	}
}

func requireMissing(t *testing.T, path string) {
	t.Helper()
	if _, err := os.Lstat(path); !os.IsNotExist(err) {
		t.Fatalf("expected %s to be absent, got %v", path, err)
	}
}
