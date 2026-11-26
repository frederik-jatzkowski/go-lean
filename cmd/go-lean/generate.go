package main

import (
	"bytes"
	"context"
	"fmt"
	"os"
	"path/filepath"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/emit"
	"github.com/frederik-jatzkowski/go-lean/internal/genfile"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
)

func generate(ctx context.Context, pattern string) ([]string, error) {
	workspace, err := readLake()
	if err != nil {
		return nil, err
	}
	source, err := load.Read(ctx, ".", pattern)
	if err != nil {
		return nil, err
	}
	checked := source.Check()
	if !checked.Complete {
		return nil, fmt.Errorf("internal error: program checking exceeded its traversal bound")
	}
	if err := checkError(checked.Failure); err != nil {
		return nil, err
	}

	program := ir.FromLoaded(checked.Program)
	if !program.Complete {
		return nil, fmt.Errorf("internal error: checked IR construction exceeded its traversal bound")
	}
	packages := make([]ir.Package, program.Packages.Size())
	for index := range packages {
		packages[index] = program.Packages.Get(uint(index)).UnwrapOr(ir.Package{})
	}

	modules := make(map[string]string)
	locations := make(map[string]location)
	owners := make(map[string]string)
	for _, p := range packages {
		loc, err := workspace.locate(p.Dir)
		if err != nil {
			return nil, err
		}
		locations[p.Path] = loc
		modules[p.Path] = emit.Module(loc.rel, p.Name)
		if owner, found := owners[modules[p.Path]]; found {
			return nil, fmt.Errorf("Go packages %s and %s map to the same Lean module", owner, p.Path)
		}
		owners[modules[p.Path]] = p.Path
	}
	type output struct {
		path     string
		artifact emit.Artifact
	}
	var outputs []output
	var targets []string
	workspace.clearSelection(pattern, locations)
	for _, p := range packages {
		loc := locations[p.Path]
		checkStem := p.Name
		if !p.Laws.IsEmpty() {
			checkStem += "_verify"
		}
		for _, artifact := range emit.Render(&p, modules) {
			outputs = append(outputs, output{path: filepath.Join(p.Dir, artifact.Stem+".lean"), artifact: artifact})
			name := loc.module(artifact.Stem)
			workspace.blocks[loc.block].roots[name] = true
			if artifact.Stem == checkStem {
				targets = append(targets, "+"+name)
			}
		}
	}
	for _, out := range outputs {
		if out.artifact.Preserve {
			continue
		}
		data, err := os.ReadFile(out.path)
		if err != nil && !os.IsNotExist(err) {
			return nil, err
		}
		if err == nil && !bytes.HasPrefix(data, []byte(emit.GeneratedHeader)) {
			return nil, fmt.Errorf("%s: generated output would overwrite a handwritten file", out.path)
		}
	}
	for _, out := range outputs {
		if out.artifact.Preserve {
			if err := createProof(out.path, out.artifact.Content); err != nil {
				return nil, err
			}
		} else if err := genfile.WriteChanged(out.path, out.artifact.Content); err != nil {
			return nil, err
		}
	}
	if err := genfile.WriteChanged("lakefile.toml", workspace.render()); err != nil {
		return nil, err
	}
	return targets, nil
}

func createProof(path, content string) error {
	f, err := os.OpenFile(path, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0o644)
	if os.IsExist(err) {
		info, statErr := os.Stat(path)
		if statErr != nil {
			return statErr
		}
		if info.Mode().IsRegular() {
			return nil
		}
		return fmt.Errorf("%s: expected a regular proof file", path)
	}
	if err != nil {
		return err
	}
	_, err = f.WriteString(content)
	closeErr := f.Close()
	if err != nil || closeErr != nil {
		_ = os.Remove(path)
		if err != nil {
			return err
		}
		return closeErr
	}
	return nil
}
