package main

import (
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"

	"github.com/pelletier/go-toml/v2"
)

const beginRoots = "# BEGIN go-lean managed roots"
const endRoots = "# END go-lean managed roots"

type rootBlock struct {
	start, end    int
	dir           string
	roots, manual map[string]bool
}

type lakeWorkspace struct {
	lines  []string
	blocks []rootBlock
	eol    string
}

func readLake() (*lakeWorkspace, error) {
	tomlFile, leanFile, err := lakeFiles()
	if err != nil {
		return nil, err
	}
	if !tomlFile || leanFile {
		return nil, fmt.Errorf("go-lean requires lakefile.toml with managed roots; run setup in a new workspace")
	}
	data, err := os.ReadFile("lakefile.toml")
	if err != nil {
		return nil, err
	}
	w := &lakeWorkspace{lines: strings.Split(string(data), "\n"), eol: "\n"}
	if strings.Contains(string(data), "\r\n") {
		w.eol = "\r\n"
	}
	config, err := decodeLake(data)
	if err != nil {
		return nil, err
	}
	start := -1
	var sanitized []string
	for i, line := range w.lines {
		switch strings.TrimSpace(line) {
		case beginRoots:
			if start >= 0 {
				return nil, fmt.Errorf("lakefile.toml: nested managed roots at line %d", i+1)
			}
			start = i
			sanitized = append(sanitized, line)
		case endRoots:
			if start < 0 {
				return nil, fmt.Errorf("lakefile.toml: unmatched managed roots at line %d", i+1)
			}
			w.blocks = append(w.blocks, rootBlock{start: start, end: i, roots: make(map[string]bool), manual: make(map[string]bool)})
			sanitized = append(sanitized, fmt.Sprintf("  '__golean_block_%d__',", len(w.blocks)-1), line)
			start = -1
		default:
			if start < 0 {
				sanitized = append(sanitized, line)
			}
		}
	}
	if start >= 0 || len(w.blocks) == 0 {
		return nil, fmt.Errorf("lakefile.toml: expected matching go-lean markers inside a lean_lib roots array")
	}
	marked, err := decodeLake([]byte(strings.Join(sanitized, "\n")))
	if err != nil {
		return nil, err
	}
	seen := make(map[int]bool)
	dirs := make(map[string]bool)
	for i, lib := range marked.Libraries {
		for j := range w.blocks {
			marker := fmt.Sprintf("__golean_block_%d__", j)
			if !slices.Contains(lib.Roots, marker) {
				continue
			}
			dir := filepath.Clean(lib.Dir)
			if seen[j] || dirs[dir] || !filepath.IsLocal(dir) {
				return nil, fmt.Errorf("lakefile.toml: expected one managed roots block per local srcDir")
			}
			seen[j], dirs[dir] = true, true
			block := &w.blocks[j]
			block.dir = dir
			for _, root := range lib.Roots {
				if root != marker {
					block.manual[root] = true
				}
			}
			for _, root := range config.Libraries[i].Roots {
				if !block.manual[root] {
					block.roots[root] = true
				}
			}
		}
	}
	if len(seen) != len(w.blocks) {
		return nil, fmt.Errorf("lakefile.toml: managed markers must be in lean_lib roots arrays")
	}
	return w, nil
}

type lakeConfig struct {
	Libraries []struct {
		Dir   string   `toml:"srcDir"`
		Roots []string `toml:"roots"`
	} `toml:"lean_lib"`
}

func decodeLake(data []byte) (lakeConfig, error) {
	var config lakeConfig
	if err := toml.Unmarshal(data, &config); err != nil {
		return config, fmt.Errorf("lakefile.toml: %w", err)
	}
	return config, nil
}

type location struct {
	block int
	rel   string
	dir   string
}

func (loc location) module(stem string) string {
	if loc.rel == "." {
		return stem
	}
	return strings.ReplaceAll(loc.rel, "/", ".") + "." + stem
}

func (w *lakeWorkspace) locate(dir string) (location, error) {
	root, err := filepath.Abs(".")
	if err != nil {
		return location{}, err
	}
	realRoot, err := filepath.EvalSymlinks(root)
	if err != nil {
		return location{}, err
	}
	realDir, err := filepath.EvalSymlinks(dir)
	if err != nil {
		return location{}, err
	}
	if rel, err := filepath.Rel(realRoot, realDir); err != nil || !filepath.IsLocal(rel) {
		return location{}, fmt.Errorf("%s resolves outside the Go module", dir)
	}
	relative, err := filepath.Rel(root, dir)
	if err != nil || !filepath.IsLocal(relative) {
		return location{}, fmt.Errorf("%s is outside the Go module", dir)
	}
	best := -1
	loc := location{dir: filepath.ToSlash(relative)}
	for i, block := range w.blocks {
		rel, err := filepath.Rel(block.dir, relative)
		if err != nil || !filepath.IsLocal(rel) || len(block.dir) <= best {
			continue
		}
		loc.block, loc.rel, best = i, filepath.ToSlash(rel), len(block.dir)
	}
	if best < 0 {
		return loc, fmt.Errorf("lakefile.toml: no managed srcDir covers %s", dir)
	}
	if loc.rel != "." {
		for _, segment := range strings.Split(loc.rel, "/") {
			if strings.ContainsAny(segment, ".'\r\n\x00«»") {
				return loc, fmt.Errorf("%s: directory segment %q cannot be used as a Lean module name", dir, segment)
			}
		}
	}
	return loc, nil
}

func (w *lakeWorkspace) clearSelection(pattern string, locations map[string]location) {
	recursive := strings.HasSuffix(pattern, "/...")
	base := strings.TrimPrefix(strings.TrimSuffix(pattern, "/..."), "./")
	for i := range w.blocks {
		block := &w.blocks[i]
		for name := range block.roots {
			parts := strings.Split(name, ".")
			dir := filepath.ToSlash(filepath.Join(append([]string{block.dir}, parts[:len(parts)-1]...)...))
			if pattern == "./..." || dir == base || (recursive && strings.HasPrefix(dir, base+"/")) {
				delete(block.roots, name)
				continue
			}
			for _, loc := range locations {
				if dir == loc.dir {
					delete(block.roots, name)
					break
				}
			}
		}
	}
}

func (w *lakeWorkspace) render() string {
	var b strings.Builder
	next := 0
	for _, block := range w.blocks {
		b.WriteString(strings.Join(w.lines[next:block.start+1], "\n") + "\n")
		for _, root := range slices.Sorted(maps.Keys(block.roots)) {
			if !block.manual[root] {
				fmt.Fprintf(&b, "  '%s',%s", root, w.eol)
			}
		}
		next = block.end
	}
	b.WriteString(strings.Join(w.lines[next:], "\n"))
	return b.String()
}
