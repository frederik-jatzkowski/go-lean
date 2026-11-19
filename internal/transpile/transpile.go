// Package transpile runs the compiler passes in order.
package transpile

import (
	"path/filepath"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
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
	return generate(programs, func(file string) (string, error) {
		return leanModule(dir, file)
	})
}

func generate(programs []gosource.Program, resolveModule func(string) (string, error)) ([]Output, error) {
	lowered := make(map[string]ir.Program, len(programs))
	roots, err := verificationRoots(programs)
	if err != nil {
		return nil, err
	}
	for _, program := range programs {
		if len(program.Roots) == 0 {
			continue
		}
		abstract := make(map[ir.Symbol]map[ir.Symbol]bool)
		for _, fn := range program.Roots {
			targets := program.Directives[fn].Abstract
			if len(targets) == 0 {
				continue
			}
			caller := rootSymbol(program, fn)
			calls := make(map[ir.Symbol]bool)
			for _, target := range targets {
				calls[abstractSymbol(caller, target.Callee)] = true
			}
			abstract[caller] = calls
		}
		checked, err := subset.Check(program)
		if err != nil {
			return nil, err
		}
		model := lower.FromSSAWithAbstractCalls(lower.NewInput(checked), sourceStem(program.Path), program.WordBits, abstract)
		if err := traceVerificationRoots(program, &model, abstract); err != nil {
			return nil, err
		}
		lowered[program.Path] = model
	}
	var outputs []Output
	for _, program := range programs {
		model := lowered[program.Path]
		verification, err := makeVerification(resolveModule, program, roots, lowered)
		if err != nil {
			return nil, err
		}
		base := strings.TrimSuffix(program.Path, ".go")
		if verification.HasModel {
			outputs = append(outputs, Output{
				Path: base + "_gen.lean", Source: lean.RenderVerification(model, verification),
			})
		}
		if len(verification.Roots) != 0 || len(verification.ScopedLaws) != 0 {
			if verification.SeparateLaws {
				outputs = append(outputs, Output{Path: base + "_laws.lean", Source: lean.RenderLaws(verification)})
			}
			outputs = append(outputs, Output{Path: base + "_verify.lean", Source: lean.RenderCheck(verification)})
		}
	}
	return outputs, nil
}

func sourceStem(path string) string {
	return strings.TrimSuffix(filepath.Base(path), ".go")
}
