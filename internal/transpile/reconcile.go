package transpile

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
)

// Reconcile generates the tree and updates any opted-in Lake libraries.
func Reconcile(dir string) error {
	root, err := filepath.Abs(dir)
	if err != nil {
		return err
	}
	data, err := readLakeFile(root)
	if err != nil {
		return err
	}
	if !bytes.Contains(data, []byte(beginRoots)) && !bytes.Contains(data, []byte(endRoots)) {
		return generateAndWrite(root)
	}
	config, packageRoot, err := parseLakeConfig(root, data)
	if err != nil {
		return err
	}
	lakefile := filepath.Join(root, "lakefile.toml")
	blocks, err := parseManagedRoots(data)
	if err != nil {
		return fmt.Errorf("%s: %w", lakefile, err)
	}
	if len(blocks) == 0 {
		return generateAndWrite(root)
	}
	entry, err := os.Lstat(lakefile)
	if err != nil {
		return err
	}
	if !entry.Mode().IsRegular() {
		return fmt.Errorf("%s: expected a regular Lake configuration file", lakefile)
	}
	if err := config.validateManagedLibraries(root, packageRoot, blocks); err != nil {
		return fmt.Errorf("%s: %w", lakefile, err)
	}

	programs, active, err := gosource.LoadWithFiles(root)
	if err != nil {
		return err
	}
	outputs, err := generate(programs, func(file string) (string, error) {
		return config.goModule(packageRoot, file)
	})
	if err != nil {
		return err
	}
	names, err := config.managedModuleNames(packageRoot, blocks, outputs)
	if err != nil {
		return err
	}
	updated, err := updateManagedRoots(data, blocks, names)
	if err != nil {
		return fmt.Errorf("%s: %w", lakefile, err)
	}
	if _, _, err := parseLakeConfig(root, updated); err != nil {
		return fmt.Errorf("updating managed roots produced invalid TOML (check commas outside the managed blocks): %w", err)
	}
	changed, err := changedOutputs(outputs)
	if err != nil {
		return err
	}
	stale, err := config.staleOutputs(root, packageRoot, blocks, outputs, active)
	if err != nil {
		return err
	}

	if err := writeOutputs(changed); err != nil {
		return err
	}
	if !bytes.Equal(data, updated) {
		current, err := os.ReadFile(lakefile)
		if err != nil {
			return err
		}
		switch {
		case bytes.Equal(current, updated):
			// Another transpile has already written these roots.
		case !bytes.Equal(current, data):
			return fmt.Errorf("%s: changed while transpiling; rerun go-lean transpile ./...", lakefile)
		default:
			if err := replace(Output{Path: lakefile, Source: string(updated)}); err != nil {
				return fmt.Errorf("%s: replace managed roots: %w", lakefile, err)
			}
		}
	}
	for _, path := range stale {
		if err := pruneOutput(path); err != nil {
			return err
		}
	}
	return nil
}

func generateAndWrite(dir string) error {
	outputs, err := Generate(dir)
	if err != nil {
		return err
	}
	return Write(outputs)
}

func (config lakeConfig) validateManagedLibraries(root, packageRoot string, blocks map[int]managedRoots) error {
	for i, library := range config.Libraries {
		if _, managed := blocks[i]; !managed {
			continue
		}
		if library.Globs != nil {
			return fmt.Errorf("library %q has managed roots and explicit globs; remove globs to build the managed roots", library.Name)
		}
		sourceRoot := filepath.Join(packageRoot, library.SrcDir)
		if !within(root, sourceRoot) || !within(packageRoot, sourceRoot) {
			return fmt.Errorf("library %q must have its managed source directory inside the project and package source directory", library.Name)
		}
		for j, other := range config.Libraries {
			if i == j {
				continue
			}
			if rel, err := filepath.Rel(sourceRoot, filepath.Join(packageRoot, other.SrcDir)); err == nil && rel == "." {
				return fmt.Errorf("libraries %q and %q share the managed source directory %s", library.Name, other.Name, sourceRoot)
			}
		}
	}
	return nil
}

func (config lakeConfig) managedModuleNames(packageRoot string, blocks map[int]managedRoots, outputs []Output) (map[int]map[string]bool, error) {
	names := make(map[int]map[string]bool)
	for _, output := range outputs {
		root, owner := config.sourceLibrary(packageRoot, output.Path)
		if _, managed := blocks[owner]; !managed {
			continue
		}
		module, err := modulePath(root, output.Path, ".lean")
		if err != nil {
			return nil, err
		}
		if names[owner] == nil {
			names[owner] = make(map[string]bool)
		}
		names[owner][lakeRoot(module)] = true
		if stem, ok := strings.CutSuffix(module, "_verify"); ok {
			names[owner][lakeRoot(stem+"_proofs")] = true
		}
	}
	return names, nil
}

func pruneOutput(path string) error {
	owned, err := generatedFile(path)
	if err != nil || !owned {
		return err
	}
	if err := os.Remove(path); err != nil && !os.IsNotExist(err) {
		return err
	}
	return nil
}
