package main

import (
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	golean "github.com/frederik-jatzkowski/go-lean"
	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
	"github.com/spf13/cobra"
	"golang.org/x/mod/modfile"
)

const skillPath = ".agents/skills/go-lean/SKILL.md"

const defaultLakefile = `name = "goLeanWorkspace"
defaultTargets = ["GoLeanProofs"]
moreLeanArgs = ["-DwarningAsError=true"]

[[lean_lib]]
name = "GoLeanProofs"
srcDir = "."
roots = [
  # BEGIN go-lean managed roots
  # END go-lean managed roots
]
`

var errDoctorFailed = errors.New("workspace checks failed")

func newSetupCommand() *cobra.Command {
	return &cobra.Command{
		Use:   "setup",
		Short: "Add missing Lean workspace files and the go-lean skill",
		Args:  cobra.NoArgs,
		RunE: func(cmd *cobra.Command, _ []string) error {
			return setupWorkspace(cmd.OutOrStdout())
		},
	}
}

func newDoctorCommand() *cobra.Command {
	var fix bool
	cmd := &cobra.Command{
		Use:   "doctor",
		Short: "Check workspace files and required tools",
		Args:  cobra.NoArgs,
		RunE: func(cmd *cobra.Command, _ []string) error {
			failed := false
			if fix && checkGoModule() == nil {
				if err := setupWorkspace(cmd.OutOrStdout()); err != nil {
					fmt.Fprintln(cmd.ErrOrStderr(), err)
					failed = true
				}
			}
			for _, err := range checkWorkspace(cmd.OutOrStdout()) {
				fmt.Fprintln(cmd.ErrOrStderr(), err)
				failed = true
			}
			if failed {
				return errDoctorFailed
			}
			fmt.Fprintln(cmd.OutOrStdout(), "go-lean workspace is ready")
			return nil
		},
	}
	cmd.Flags().BoolVar(&fix, "fix", false, "Create missing workspace files")
	return cmd
}

func checkGoModule() error {
	data, err := os.ReadFile("go.mod")
	if os.IsNotExist(err) {
		return errors.New("go.mod is missing: run from the Go module root or initialize it with go mod init")
	}
	if err != nil {
		return err
	}
	mod, err := modfile.Parse("go.mod", data, nil)
	if err != nil {
		return err
	}
	if mod.Module == nil || mod.Module.Mod.Path == "" {
		return errors.New("go.mod: add a module directive")
	}
	return nil
}

func lakeFiles() (toml, lean bool, err error) {
	toml, tomlErr := fileExists("lakefile.toml")
	lean, leanErr := fileExists("lakefile.lean")
	return toml, lean, errors.Join(tomlErr, leanErr)
}

func fileExists(path string) (bool, error) {
	_, err := os.Lstat(path)
	if os.IsNotExist(err) {
		return false, nil
	}
	return err == nil, err
}

func setupWorkspace(out io.Writer) error {
	if err := checkGoModule(); err != nil {
		return err
	}
	toml, lean, lakeErr := lakeFiles()
	const repoDocs = "https://github.com/frederik-jatzkowski/go-lean/blob/main/"
	skill := strings.ReplaceAll(golean.Skill, "](../../../", "]("+repoDocs)
	err := errors.Join(lakeErr,
		createScaffold(out, "lean-toolchain", golean.LeanToolchain),
		createScaffold(out, skillPath, skill))
	if lakeErr == nil && !toml && !lean {
		err = errors.Join(err, createScaffold(out, "lakefile.toml", defaultLakefile))
	}
	return err
}

func createScaffold(out io.Writer, path, content string) error {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	f, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o644)
	if os.IsExist(err) {
		return nil
	}
	if err != nil {
		return err
	}
	_, writeErr := f.WriteString(content)
	if err := errors.Join(writeErr, f.Close()); err != nil {
		return errors.Join(err, os.Remove(path))
	}
	fmt.Fprintln(out, "Created", path)
	return nil
}

func checkWorkspace(out io.Writer) []error {
	var issues []error
	if err := checkGoModule(); err != nil {
		issues = append(issues, err)
	}
	for _, path := range []string{"lean-toolchain", skillPath} {
		data, err := os.ReadFile(path)
		switch {
		case os.IsNotExist(err):
			issues = append(issues, fmt.Errorf("%s is missing: run go-lean setup", path))
		case err != nil:
			issues = append(issues, err)
		case strings.TrimSpace(string(data)) == "":
			issues = append(issues, fmt.Errorf("%s is empty: supply its contents or move it aside and run go-lean setup", path))
		case path == "lean-toolchain" && len(strings.Fields(string(data))) != 1:
			issues = append(issues, errors.New("lean-toolchain: specify one Lean toolchain"))
		}
	}
	toml, lean, err := lakeFiles()
	switch {
	case err != nil:
		issues = append(issues, err)
	case toml && lean:
		issues = append(issues, errors.New("both lakefile.toml and lakefile.lean exist: keep one Lake configuration"))
	case toml:
		managed, err := transpile.CheckLakeTOML(".")
		if err != nil {
			issues = append(issues, err)
		} else if !managed {
			fmt.Fprintln(out, "Register generated modules in the Lake configuration when using manual roots.")
		}
	case lean:
		data, err := os.ReadFile("lakefile.lean")
		if err != nil {
			issues = append(issues, err)
		} else if strings.TrimSpace(string(data)) == "" {
			issues = append(issues, errors.New("lakefile.lean is empty: configure a Lake library for the generated modules"))
		} else {
			fmt.Fprintln(out, "Register generated modules in lakefile.lean when using manual roots.")
		}
	default:
		issues = append(issues, errors.New("Lake configuration is missing: run go-lean setup"))
	}
	for _, tool := range []string{"go", "lake", "lean"} {
		if _, err := exec.LookPath(tool); err != nil {
			guide := "https://lean-lang.org/install/manual/"
			if tool == "go" {
				guide = "https://go.dev/doc/install"
			}
			issues = append(issues, fmt.Errorf("%s is unavailable on PATH: see %s", tool, guide))
		}
	}
	return issues
}
