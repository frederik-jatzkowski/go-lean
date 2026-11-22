package transpile

import (
	"bytes"
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
)

// Reconcile generates the tree and updates any opted-in Lake libraries.
func Reconcile(dir string) error {
	_, err := ReconcilePattern(dir, "./...")
	return err
}

// ReconcilePattern generates the selected packages and returns focused Lake targets.
func ReconcilePattern(dir, pattern string) ([]string, error) {
	focused := pattern != "./..."
	root, err := filepath.Abs(dir)
	if err != nil {
		return nil, err
	}
	config, packageRoot, data, blocks, err := workspaceLakeConfig(root)
	if err != nil {
		return nil, err
	}
	programs, active, err := gosource.LoadWithFiles(root, pattern)
	if err != nil {
		return nil, err
	}
	outputs, err := generate(programs, func(file string) (string, error) {
		return config.goModule(packageRoot, file)
	})
	if err != nil {
		return nil, err
	}
	var targets []string
	if focused {
		targets, err = config.verificationTargets(packageRoot, outputs)
		if err != nil {
			return nil, err
		}
	}
	if len(blocks) == 0 {
		return targets, Write(outputs)
	}
	return targets, reconcileManaged(root, packageRoot, config, data, blocks, outputs, active, focused)
}

func reconcileManaged(root, packageRoot string, config lakeConfig, data []byte, blocks map[int]managedRoots, outputs []Output, active map[string]bool, focused bool) error {
	lakefile := filepath.Join(root, "lakefile.toml")
	names, err := config.managedModuleNames(packageRoot, blocks, outputs)
	if err != nil {
		return err
	}
	if focused {
		var selected []Output
		for _, output := range outputs {
			if stem, ok := strings.CutSuffix(output.Path, "_model.lean"); ok {
				selected = append(selected, Output{Path: stem + "_decreases.lean"}, Output{Path: stem + "_decreases_proofs.lean"})
			}
		}
		for source := range active {
			stem := strings.TrimSuffix(source, ".go")
			for _, suffix := range []string{"_gen.lean", "_laws.lean", "_verify.lean"} {
				selected = append(selected, Output{Path: stem + suffix})
			}
		}
		selectedNames, err := config.managedModuleNames(packageRoot, blocks, selected)
		if err != nil {
			return err
		}
		for i, block := range blocks {
			if names[i] == nil {
				names[i] = make(map[string]bool)
			}
			for _, name := range block.generated {
				if !selectedNames[i][name] {
					names[i][name] = true
				}
			}
		}
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
	stale, err := config.staleOutputs(root, packageRoot, blocks, outputs, active, focused)
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

func (config lakeConfig) verificationTargets(packageRoot string, outputs []Output) ([]string, error) {
	files := make(map[string]string)
	models := make(map[string]string)
	wrapped := make(map[string]bool)
	for _, output := range outputs {
		stem, check := strings.CutSuffix(output.Path, "_verify.lean")
		if check {
			files[stem] = output.Path
			wrapped[filepath.Dir(output.Path)] = true
		} else if stem, model := strings.CutSuffix(output.Path, "_gen.lean"); model && files[stem] == "" {
			files[stem] = output.Path
			wrapped[filepath.Dir(output.Path)] = true
		} else if strings.HasSuffix(output.Path, "_model.lean") {
			models[filepath.Dir(output.Path)] = output.Path
		}
	}
	for dir, model := range models {
		if !wrapped[dir] {
			files[model] = model
		}
	}
	targets := make(map[string]bool)
	for _, file := range files {
		root, _ := config.sourceLibrary(packageRoot, file)
		module, err := modulePath(root, file, ".lean")
		if err != nil {
			return nil, err
		}
		targets["+"+lakeRoot(module)] = true
	}
	return slices.Sorted(maps.Keys(targets)), nil
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
		if strings.HasSuffix(module, "_decreases") {
			proof := strings.TrimSuffix(output.Path, ".lean") + "_proofs.lean"
			if _, err := os.Stat(proof); err == nil {
				names[owner][lakeRoot(module+"_proofs")] = true
			} else if !os.IsNotExist(err) {
				return nil, err
			}
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
