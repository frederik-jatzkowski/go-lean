package genfile

import (
	"os"
	"path/filepath"
)

// WriteChanged atomically replaces a generated file when its contents change.
func WriteChanged(path, content string) error {
	old, err := os.ReadFile(path)
	if err == nil && string(old) == content {
		return nil
	}
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	f, err := os.CreateTemp(filepath.Dir(path), ".golean-*")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	_, err = f.WriteString(content)
	closeErr := f.Close()
	if err != nil {
		return err
	}
	if closeErr != nil {
		return closeErr
	}
	return os.Rename(f.Name(), path)
}
