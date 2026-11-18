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
		Short:         "Translate pure Go int64 functions into Lean 4",
		SilenceUsage:  true,
		SilenceErrors: true,
	}

	transpileCmd := &cobra.Command{
		Use:   "transpile ./...",
		Short: "Generate Lean definitions beside Go files marked with //golean:verify",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if args[0] != "./..." {
				return errors.New("use go-lean transpile ./...")
			}
			outputs, err := transpile.Generate(".")
			if err != nil {
				return err
			}
			return transpile.Write(outputs)
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
