// Package transpile runs the compiler passes in order.
package transpile

import (
	"path/filepath"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/lean"
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
	roots, err := verificationRoots(programs)
	if err != nil {
		return nil, err
	}
	models, ordered, lowered, err := packageModels(programs)
	if err != nil {
		return nil, err
	}
	verification := make(map[string]lean.Verification, len(programs))
	for _, program := range programs {
		file, err := makeVerification(resolveModule, program, roots, lowered)
		if err != nil {
			return nil, err
		}
		verification[program.Path] = file
		pkg := models[file.Scope.Package]
		pkg.addVerification(file)
	}
	var outputs []Output
	for _, model := range ordered {
		if model.hasDefinitions() {
			module, err := resolveModule(model.path + ".go")
			if err != nil {
				return nil, err
			}
			model.module = lean.PackageModule(module)
			outputs = append(outputs, model.output(models))
		}
	}
	for _, program := range programs {
		v := verification[program.Path]
		model := models[v.Scope.Package]
		v.ModelModule = model.module
		base := strings.TrimSuffix(program.Path, ".go")
		if v.HasModel {
			outputs = append(outputs, Output{
				Path: base + "_gen.lean", Source: lean.RenderAliases(model.program, v, model.module, model.visibleFunctions()),
			})
		}
		if len(v.Roots) != 0 || len(v.ScopedLaws) != 0 {
			if v.SeparateLaws {
				outputs = append(outputs, Output{Path: base + "_laws.lean", Source: lean.RenderLaws(v)})
			}
			outputs = append(outputs, Output{Path: base + "_verify.lean", Source: lean.RenderCheck(v)})
		}
	}
	return outputs, nil
}

func sourceStem(path string) string {
	return strings.TrimSuffix(filepath.Base(path), ".go")
}
