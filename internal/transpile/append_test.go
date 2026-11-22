package transpile_test

import (
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

const appendFold = `func collect(input, other []uint8) ([]uint16, bool) {
	out := make([]uint16, 0, len(input))
	valid := true
	for _, b := range input {
		if b == 0 {
			valid = false
		} else if b < 10 {
			value := uint16(b)
			out = append(out, value)
		} else {
			out = append(out, 100)
		}
	}
	return out, valid
}
`

func TestAppendFoldPreservesCapacityThroughCalls(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), "package sample\n"+appendFold+`
//golean:export
func observe(input []uint8) (uint16, int, int, bool) {
	out, valid := collect(input, nil)
	var sum uint16
	// The empty result remains non-nil and keeps its allocated capacity.
	if len(out) != 0 {
		sum = out[0]
	}
	return sum, len(out), cap(out), valid
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	checkGeneratedLean(t, dir, outputs[0].Path, outputs[0].Source, `
open GoLean.«example.test/sample»

example : collect [0, 3, 10] [] = (some ([3, 100], 3), false) := by decide
example : observe [0, 0] = some (0, 0, 2, false) := by decide
example : observe [11, 4] = some (100, 2, 2, true) := by decide
`)
}

func TestAppendFoldRejectsUnsupportedOwnership(t *testing.T) {
	for _, test := range []struct {
		name, old, replacement, extra, want string
	}{
		{"observable growth", "len(input)", "len(other)", "//golean:export\nfunc capacity(input []uint8) int { out, _ := collect(input, nil); return cap(out) }", "append with observable capacity"},
		{"caller write", "valid = false", "valid = false; input[0] = 3", "", "slice elements are read-only"},
		{"escape", "out = append(out, value)", "out = append(out, value); saved = out", "var saved []uint16", "cannot write collection after publication"},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := newModule(t)
			source := strings.Replace(appendFold, test.old, test.replacement, 1)
			writeFile(t, filepath.Join(dir, "input.go"), "package sample\n//golean:export\n"+source+test.extra+"\n")
			if _, err := transpile.Generate(dir); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("expected %q, got %v", test.want, err)
			}
		})
	}
}
