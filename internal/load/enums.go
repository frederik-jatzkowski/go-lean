package load

import (
	"fmt"
	"go/ast"
	"go/types"
	"os"
	"path/filepath"

	"github.com/frederik-jatzkowski/go-lean/internal/enums"
	"golang.org/x/tools/go/packages"
)

type Enum struct {
	Spec     enums.Spec
	Payloads []*types.TypeName
}

type EnumConstructor struct {
	Owner   *types.TypeName
	Variant string
}

func (program *Program) readEnums(p *packages.Package, files []*ast.File) (*ast.File, error) {
	var generated *ast.File
	var specs []enums.Spec
	for _, file := range files {
		path := p.Fset.PositionFor(file.Pos(), false).Filename
		if filepath.Base(path) == enums.File {
			generated = file
			continue
		}
		found, err := enums.Read(file.Doc, p.Fset)
		if err != nil {
			return nil, err
		}
		specs = append(specs, found...)
	}
	if generated == nil && len(specs) == 0 {
		return nil, nil
	}
	path := filepath.Join(Dir(p), enums.File)
	actual, err := os.ReadFile(path)
	if generated == nil || err != nil {
		return nil, enums.Stale(path)
	}
	if len(specs) == 0 {
		if enums.Owns(actual) {
			return nil, enums.Stale(path)
		}
		return nil, nil
	}
	expected, err := enums.Render(p.Name, specs)
	if err != nil {
		return nil, err
	}
	if !enums.Matches(actual, expected) {
		return nil, enums.Stale(path)
	}

	for _, spec := range specs {
		owner, ok := p.Types.Scope().Lookup(spec.Name).(*types.TypeName)
		if !ok || owner.IsAlias() {
			return nil, fmt.Errorf("%s: invalid generated enum %s", path, spec.Name)
		}
		entry := Enum{Spec: spec}
		for _, name := range spec.Cases {
			obj, ok := p.Types.Scope().Lookup(name).(*types.TypeName)
			if !ok || obj.IsAlias() {
				return nil, fmt.Errorf("%s: invalid enum payload %s", path, name)
			}
			named := obj.Type().(*types.Named)
			switch named.Underlying().(type) {
			case *types.Basic, *types.Struct:
			default:
				return nil, Error(p, obj.Pos(), "unsupported enum payload %s", name)
			}
			if named.TypeParams().Len() != 0 {
				return nil, Error(p, obj.Pos(), "generic enum payload %s", name)
			}
			entry.Payloads = append(entry.Payloads, obj)
			fn := p.Types.Scope().Lookup(spec.Constructor(name)).(*types.Func)
			program.EnumConstructors[fn] = EnumConstructor{Owner: owner, Variant: name}
		}
		typ := owner.Type().(*types.Named)
		for method := range typ.Methods() {
			if method.Name() == "Case" {
				program.EnumCases[method] = owner
				break
			}
		}
		program.Enums[owner] = entry
	}
	return generated, nil
}
