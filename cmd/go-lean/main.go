package main

import (
	"errors"
	"fmt"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/enums"
	"github.com/spf13/cobra"
)

func newCommand() *cobra.Command {
	root := &cobra.Command{
		Use:           "go-lean",
		Short:         "Translate supported Go functions and methods into Lean 4",
		SilenceUsage:  true,
		SilenceErrors: true,
	}

	transpileCmd := &cobra.Command{
		Use:   "transpile <path>",
		Short: "Generate Lean models and checks from go-lean directives",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if err := validatePattern(args[0]); err != nil {
				return err
			}
			_, err := generate(cmd.Context(), args[0])
			return err
		},
	}
	root.AddCommand(&cobra.Command{
		Use: "generate <path>", Short: "Generate Go enum declarations", Args: cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if err := validatePattern(args[0]); err != nil {
				return err
			}
			return enums.Process(cmd.Context(), ".", args[0], true)
		},
	}, transpileCmd, newVerifyCommand(), newSetupCommand(), newDoctorCommand())
	root.CompletionOptions.DisableDefaultCmd = true
	return root
}

func validatePattern(pattern string) error {
	if pattern == "." || pattern == "./..." {
		return nil
	}
	dir, local := strings.CutPrefix(pattern, "./")
	dir = strings.TrimSuffix(dir, "/...")
	if !local || dir == "." || !fs.ValidPath(dir) || strings.Contains(dir, "...") ||
		strings.ContainsAny(dir, "\\:") {
		return fmt.Errorf("invalid package path %q: use ., ./pkg, ./pkg/..., or ./...", pattern)
	}
	info, err := os.Stat(dir)
	if err != nil {
		return err
	}
	if !info.IsDir() {
		return fmt.Errorf("%s: expected a Go package directory", dir)
	}
	root, err := filepath.Abs(".")
	if err != nil {
		return err
	}
	root, err = filepath.EvalSymlinks(root)
	if err != nil {
		return err
	}
	resolved, err := filepath.EvalSymlinks(filepath.Join(root, dir))
	if err != nil {
		return err
	}
	relative, err := filepath.Rel(root, resolved)
	if err != nil || !filepath.IsLocal(relative) {
		return fmt.Errorf("package path %q resolves outside the Go module", pattern)
	}
	return nil
}

func newVerifyCommand() *cobra.Command {
	return &cobra.Command{
		Use:   "verify [path]",
		Short: "Generate Lean modules and check them with Lake",
		Args:  cobra.MaximumNArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			pattern := "./..."
			if len(args) != 0 {
				pattern = args[0]
			}
			if err := validatePattern(pattern); err != nil {
				return err
			}
			targets, err := generate(cmd.Context(), pattern)
			if err != nil {
				return err
			}
			if len(targets) == 0 {
				fmt.Fprintln(cmd.OutOrStdout(), "No Lean targets for", pattern)
				return nil
			}
			lake := exec.CommandContext(cmd.Context(), "lake", append([]string{"build"}, targets...)...)
			lake.Stdin = cmd.InOrStdin()
			lake.Stdout = cmd.OutOrStdout()
			lake.Stderr = cmd.ErrOrStderr()
			if err := lake.Run(); err != nil {
				var exit *exec.ExitError
				if errors.As(err, &exit) && exit.ExitCode() >= 0 {
					return exit
				}
				return fmt.Errorf("lake build: %v", err)
			}
			return nil
		},
	}
}

func main() {
	if err := newCommand().Execute(); err != nil {
		var exit *exec.ExitError
		if errors.As(err, &exit) {
			os.Exit(exit.ExitCode())
		}
		if !errors.Is(err, errDoctorFailed) {
			fmt.Fprintln(os.Stderr, err)
		}
		os.Exit(1)
	}
}
