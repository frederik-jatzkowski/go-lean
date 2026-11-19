package transpile

import (
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"

	"github.com/pelletier/go-toml/v2"
)

type lakeConfig struct {
	SrcDir    string        `toml:"srcDir"`
	Libraries []lakeLibrary `toml:"lean_lib"`
}

type lakeLibrary struct {
	Name   string `toml:"name"`
	SrcDir string `toml:"srcDir"`
	Globs  any    `toml:"globs"`
}

func readLakeFile(dir string) ([]byte, error) {
	data, err := os.ReadFile(filepath.Join(dir, "lakefile.toml"))
	if os.IsNotExist(err) {
		return nil, nil
	}
	return data, err
}

func parseLakeConfig(dir string, data []byte) (lakeConfig, string, error) {
	var config lakeConfig
	if err := toml.Unmarshal(data, &config); err != nil {
		return config, "", fmt.Errorf("%s: %w", filepath.Join(dir, "lakefile.toml"), err)
	}
	return config, filepath.Join(dir, config.SrcDir), nil
}

func within(root, path string) bool {
	relative, err := filepath.Rel(root, path)
	return err == nil && filepath.IsLocal(relative)
}

// sourceLibrary selects the most specific configured Lake source directory.
// A library at the package source root also owns modules at that root.
func (config lakeConfig) sourceLibrary(packageRoot, path string) (string, int) {
	sourceRoot, owner := packageRoot, -1
	for i, lib := range config.Libraries {
		candidate := filepath.Join(packageRoot, lib.SrcDir)
		if (len(candidate) > len(sourceRoot) || owner == -1 && len(candidate) == len(sourceRoot)) && within(candidate, path) {
			sourceRoot, owner = candidate, i
		}
	}
	return sourceRoot, owner
}

func leanModule(dir, file string) (string, error) {
	projectRoot, err := filepath.Abs(dir)
	if err != nil {
		return "", err
	}
	data, err := readLakeFile(projectRoot)
	if err != nil {
		return "", err
	}
	config, packageRoot, err := parseLakeConfig(projectRoot, data)
	if err != nil {
		return "", err
	}
	return config.goModule(packageRoot, file)
}

func (config lakeConfig) goModule(packageRoot, file string) (string, error) {
	sourceRoot, _ := config.sourceLibrary(packageRoot, file)
	return modulePath(sourceRoot, file, ".go")
}

func modulePath(root, file, extension string) (string, error) {
	relative, err := filepath.Rel(root, file)
	if err != nil || !filepath.IsLocal(relative) {
		return "", fmt.Errorf("%s: cannot determine Lean module relative to %s", file, root)
	}
	module := filepath.ToSlash(strings.TrimSuffix(relative, extension))
	if strings.ContainsAny(module, "«»\n\r") {
		return "", fmt.Errorf("%s: unsupported Lean module path", file)
	}
	return module, nil
}

func (config lakeConfig) staleOutputs(projectRoot, packageRoot string, blocks map[int]managedRoots, outputs []Output, active map[string]bool) ([]string, error) {
	expected := make(map[string]bool, len(outputs))
	for _, output := range outputs {
		expected[output.Path] = true
	}
	var roots []string
	for i := range blocks {
		roots = append(roots, filepath.Join(packageRoot, config.Libraries[i].SrcDir))
	}

	var stale []string
	err := fs.WalkDir(os.DirFS(projectRoot), ".", func(relative string, entry fs.DirEntry, err error) error {
		path := filepath.Join(projectRoot, filepath.FromSlash(relative))
		if err != nil {
			return fmt.Errorf("%s: %w", path, err)
		}
		if entry.IsDir() {
			if relative == "." {
				return nil
			}
			name := entry.Name()
			if name == "vendor" || strings.HasPrefix(name, ".") || entry.Type()&fs.ModeSymlink != 0 {
				return fs.SkipDir
			}
			_, owner := config.sourceLibrary(packageRoot, path)
			_, relevant := blocks[owner]
			for _, root := range roots {
				if within(path, root) {
					relevant = true
					break
				}
			}
			if !relevant {
				return fs.SkipDir
			}
			if _, err := os.Lstat(filepath.Join(path, "go.mod")); err == nil {
				return fs.SkipDir
			} else if !os.IsNotExist(err) {
				return err
			}
			return nil
		}
		if !entry.Type().IsRegular() || expected[path] {
			return nil
		}
		stem, ok := generatedStem(path)
		if !ok {
			return nil
		}
		_, owner := config.sourceLibrary(packageRoot, path)
		if _, managed := blocks[owner]; !managed {
			return nil
		}
		source := stem + ".go"
		if !active[source] {
			if _, err := os.Lstat(source); err == nil {
				return nil
			} else if !os.IsNotExist(err) {
				return err
			}
		}
		owned, err := generatedFile(path)
		if err != nil {
			return err
		}
		if owned {
			stale = append(stale, path)
		}
		return nil
	})
	return stale, err
}

func generatedFile(path string) (bool, error) {
	info, err := os.Lstat(path)
	if os.IsNotExist(err) {
		return false, nil
	}
	if err != nil || !info.Mode().IsRegular() {
		return false, err
	}
	data, err := os.ReadFile(path)
	if os.IsNotExist(err) {
		return false, nil
	}
	return err == nil && hasGeneratedHeader(string(data)), err
}

func generatedStem(path string) (string, bool) {
	for _, suffix := range []string{"_gen.lean", "_laws.lean", "_verify.lean"} {
		if stem, ok := strings.CutSuffix(path, suffix); ok {
			return stem, true
		}
	}
	return "", false
}
