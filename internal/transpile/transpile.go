// Package transpile runs the compiler passes in order.
package transpile

import (
	"path/filepath"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/lean"
	"github.com/frederik-jatzkowski/go-lean/internal/lower"
	"github.com/frederik-jatzkowski/go-lean/internal/subset"
)

type Output struct {
	Path   string
	Source string
}

// Generate runs every compiler pass before any generated file is written.
func Generate(dir string) ([]Output, error) {
	programs, err := gosource.Load(dir)
	if err != nil {
		return nil, err
	}
	outputs := make([]Output, 0, len(programs))
	for _, program := range programs {
		checked, err := subset.Check(program)
		if err != nil {
			return nil, err
		}
		stem := strings.TrimSuffix(filepath.Base(program.Path), ".go")
		outputs = append(outputs, Output{
			Path:   filepath.Join(filepath.Dir(program.Path), stem+"_gen.lean"),
			Source: lean.Render(lower.FromSSA(checked, stem, program.WordBits)),
		})
	}
	return outputs, nil
}
