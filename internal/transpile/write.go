package transpile

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/lean"
)

// Write checks all destinations before replacing any changed generated files.
func Write(outputs []Output) error {
	var changed []Output
	for _, output := range outputs {
		existing, err := os.Lstat(output.Path)
		if os.IsNotExist(err) {
			changed = append(changed, output)
			continue
		}
		if err != nil {
			return err
		}
		if !existing.Mode().IsRegular() {
			return fmt.Errorf("%s: expected a regular generated file", output.Path)
		}
		current, err := os.ReadFile(output.Path)
		if err != nil {
			return err
		}
		line, _, _ := strings.Cut(string(current), "\n")
		if strings.TrimSuffix(line, "\r") != lean.GeneratedHeader {
			return fmt.Errorf("%s: refusing to overwrite a file without the go-lean generated header", output.Path)
		}
		if string(current) != output.Source {
			changed = append(changed, output)
		}
	}
	for _, output := range changed {
		if err := replace(output); err != nil {
			return err
		}
	}
	return nil
}

func replace(output Output) error {
	file, err := os.CreateTemp(filepath.Dir(output.Path), ".go-lean-*")
	if err != nil {
		return err
	}
	defer os.Remove(file.Name())
	_, writeErr := file.WriteString(output.Source)
	closeErr := file.Close()
	if writeErr != nil {
		return writeErr
	}
	if closeErr != nil {
		return closeErr
	}
	if err := os.Chmod(file.Name(), 0o644); err != nil {
		return err
	}
	return os.Rename(file.Name(), output.Path)
}
