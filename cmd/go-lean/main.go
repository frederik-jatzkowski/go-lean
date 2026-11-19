package main

import (
	"errors"
	"fmt"
	"os"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
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
		Use:   "transpile ./...",
		Short: "Generate Lean models and checks from go-lean directives",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if args[0] != "./..." {
				return errors.New("use go-lean transpile ./...")
			}
			return transpile.Reconcile(".")
		},
	}
	root.AddCommand(transpileCmd)
	root.CompletionOptions.DisableDefaultCmd = true
	return root
}

func main() {
	if err := newCommand().Execute(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
