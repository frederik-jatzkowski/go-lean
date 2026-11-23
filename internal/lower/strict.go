package lower

import (
	"go/ast"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"golang.org/x/tools/go/packages"
)

func (c *compiler) checkPackage(p *packages.Package) error {
	variants := make(map[string]bool)
	for _, enum := range c.source.Enums[p.PkgPath] {
		for _, name := range enum.Variants {
			variants[name] = true
		}
	}
	for _, file := range p.Syntax {
		if _, generated := c.source.EnumFiles[p.Fset.PositionFor(file.Pos(), false).Filename]; generated {
			continue
		}
		for _, spec := range file.Imports {
			if spec.Name != nil && spec.Name.Name == "_" {
				return load.Error(p, spec.Pos(), "blank imports are unsupported in modeled packages")
			}
		}
		for _, declaration := range file.Decls {
			switch decl := declaration.(type) {
			case *ast.GenDecl:
				for _, spec := range decl.Specs {
					switch spec := spec.(type) {
					case *ast.TypeSpec:
						if spec.Name.IsExported() || spec.Assign.IsValid() || spec.TypeParams != nil {
							return load.Error(p, spec.Pos(), "modeled data types must be private, defined, and nongeneric")
						}
						if record, ok := spec.Type.(*ast.StructType); ok {
							for _, field := range record.Fields.List {
								for _, name := range field.Names {
									if name.IsExported() {
										return load.Error(p, name.Pos(), "modeled record fields must be private")
									}
								}
							}
						}
						if variants[spec.Name.Name] {
							continue
						}
						obj := p.TypesInfo.Defs[spec.Name].(*types.TypeName)
						if _, err := c.goType(p, spec.Pos(), obj.Type()); err != nil {
							return err
						}
					case *ast.ValueSpec:
						if decl.Tok == token.VAR {
							return load.Error(p, spec.Pos(), "package variables are unsupported in modeled packages")
						}
						for _, name := range spec.Names {
							if obj := p.TypesInfo.Defs[name]; obj != nil {
								if _, err := c.goType(p, name.Pos(), obj.Type()); err != nil {
									return err
								}
							}
						}
					}
				}
			case *ast.FuncDecl:
				if decl.Name.Name == "init" && decl.Recv == nil {
					return load.Error(p, decl.Pos(), "initialization hooks are unsupported in modeled packages")
				}
				fn, ok := p.TypesInfo.Defs[decl.Name].(*types.Func)
				if !ok {
					return load.Error(p, decl.Pos(), "expected a named modeled function")
				}
				if fn.Exported() {
					sig := fn.Signature()
					if sig.Recv() != nil && c.containsEnum(sig.Recv().Type(), make(map[types.Type]bool)) {
						return load.Error(p, decl.Pos(), "public methods on enum-containing types require a checked function entry point")
					}
					params := sig.Params()
					for i := range params.Len() {
						if c.containsEnum(params.At(i).Type(), make(map[types.Type]bool)) {
							return load.Error(p, decl.Pos(), "public operations accepting enums require a private golean:export implementation")
						}
					}
				}
				c.roots = append(c.roots, fn)
			}
		}
	}
	return nil
}

func (c *compiler) containsEnum(typ types.Type, seen map[types.Type]bool) bool {
	typ = types.Unalias(typ)
	if seen[typ] {
		return false
	}
	seen[typ] = true
	if named, ok := typ.(*types.Named); ok {
		obj := named.Obj()
		if obj.Pkg() != nil {
			for _, enum := range c.source.Enums[obj.Pkg().Path()] {
				if enum.Name == obj.Name() {
					return true
				}
			}
		}
		for i := range named.TypeArgs().Len() {
			if c.containsEnum(named.TypeArgs().At(i), seen) {
				return true
			}
		}
	}
	if record, ok := typ.Underlying().(*types.Struct); ok {
		for i := range record.NumFields() {
			if c.containsEnum(record.Field(i).Type(), seen) {
				return true
			}
		}
	}
	return false
}
