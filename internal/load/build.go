package load

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
	"golang.org/x/tools/go/packages"
)

func build(roots []*packages.Package) (loaded.Program, error) {
	var program loaded.Program
	objects := []loaded.Object{{}}
	typeTable := []loaded.Type{{}}
	expressions := []loaded.Expression{{}}
	statements := []loaded.Statement{{}}
	objectIDs := make(map[types.Object]loaded.ObjectID)
	typeIDs := make(map[types.Type]loaded.TypeID)
	packagesByPath := make(map[string]*packages.Package)
	packages.Visit(roots, nil, func(p *packages.Package) { packagesByPath[p.PkgPath] = p })
	var typeID func(types.Type) loaded.TypeID
	objectID := func(obj types.Object) loaded.ObjectID {
		if obj == nil {
			return 0
		}
		if id, ok := objectIDs[obj]; ok {
			return id
		}
		// Reserve the ID before following types, which can refer back to this object.
		id := loaded.ObjectID(len(objects))
		objectIDs[obj] = id
		objects = append(objects, loaded.Object{})
		entry := loaded.Object{Name: obj.Name()}
		if pkg := obj.Pkg(); pkg != nil {
			entry.Package = pkg.Path()
			if p := packagesByPath[entry.Package]; p != nil {
				entry.Pos = p.Fset.Position(obj.Pos()).String()
			}
		}
		entry.Type = typeID(obj.Type())
		switch obj := obj.(type) {
		case *types.TypeName:
			entry.Kind = loaded.TypeName
		case *types.Func:
			entry.Kind = loaded.FunctionObject
			entry.FullName = obj.FullName()
		case *types.Var:
			entry.Kind = loaded.Variable
			entry.Embedded = obj.Embedded()
		case *types.Const:
			entry.Kind = loaded.ConstantObject
			entry.Value = constantValue(obj.Val())
			entry.DefaultType = typeID(types.Default(obj.Type()))
		}
		objects[id] = entry
		return id
	}
	typeID = func(typ types.Type) loaded.TypeID {
		if typ == nil {
			return 0
		}
		if id, ok := typeIDs[typ]; ok {
			return id
		}
		id := loaded.TypeID(len(typeTable))
		typeIDs[typ] = id
		typeTable = append(typeTable, loaded.Type{})
		typeTable[id] = readType(typ, typeID, objectID)
		return id
	}
	requested := make(map[string]bool)
	for _, p := range roots {
		requested[p.ID] = true
	}
	var selected, diagnostics []string
	packages.Visit(roots, nil, func(p *packages.Package) {
		entry := loaded.Package{Path: p.PkgPath, Name: p.Name, Dir: packageDir(p), WordBits: 64}
		if p.Module != nil {
			entry.Module = p.Module.Path
		}
		if p.TypesSizes.Sizeof(types.Typ[types.Uint]) == 4 {
			entry.WordBits = 32
		}

		files := slices.Clone(p.Syntax)
		slices.SortFunc(files, func(a, b *ast.File) int {
			return strings.Compare(p.Fset.PositionFor(a.Pos(), false).Filename, p.Fset.PositionFor(b.Pos(), false).Filename)
		})
		generated, err := readEnums(p, files, objectID, &objects)
		if err != nil {
			entry.Issue = err.Error()
			if requested[p.ID] {
				diagnostics = append(diagnostics, entry.Issue)
			}
			program.Packages = program.Packages.Insert(p.PkgPath, entry)
			return
		}
		var laws []loaded.Proposition
		var imports []string
		var marked bool
		for _, file := range files {
			if file == generated {
				continue
			}
			if entry.Issue == "" {
				laws, imports, entry.Issue = readPackageDirectives(p, file.Doc, laws, imports)
			}
			for _, raw := range file.Decls {
				d, ok := raw.(*ast.FuncDecl)
				if !ok || d.Doc == nil {
					continue
				}
				fn, ok := p.TypesInfo.Defs[d.Name].(*types.Func)
				if !ok {
					continue
				}
				meta := readDirectives(p, file, d, objectID)
				if meta.Selected || meta.Assumptions.Size() != 0 || meta.Issue != "" {
					id := objectID(fn)
					objects[id].Function = lean.Some(meta)
				}
				marked = marked || meta.Selected
			}
		}
		entry.Modeled = p.PkgPath != loaded.Curated && (marked || generated != nil || len(laws) != 0)
		if entry.Modeled {
			entry.Declarations = readDeclarations(p, files, generated, objectID, typeID, &objects, &expressions, &statements)
			if requested[p.ID] {
				selected = append(selected, p.PkgPath)
			}
		} else {
			// A referenced type may belong to an otherwise unmodeled dependency.
			for _, file := range files {
				for _, raw := range file.Decls {
					d, ok := raw.(*ast.GenDecl)
					if !ok || d.Tok != token.TYPE {
						continue
					}
					for _, raw := range d.Specs {
						spec := raw.(*ast.TypeSpec)
						if pos := firstDirective(d.Doc, spec.Doc); pos.IsValid() {
							id := objectID(p.TypesInfo.Defs[spec.Name])
							objects[id].Issue = sourceError(p, pos, "type directives are unsupported; attach laws to functions")
						}
					}
				}
			}
		}
		entry.Laws = lean.ArrayFromSlice(laws)
		entry.LeanImports = lean.ArrayFromSlice(imports)
		if requested[p.ID] && entry.Issue != "" {
			diagnostics = append(diagnostics, entry.Issue)
		}
		program.Packages = program.Packages.Insert(p.PkgPath, entry)
	})
	if len(diagnostics) != 0 {
		slices.Sort(diagnostics)
		return loaded.Program{}, fmt.Errorf("%s", diagnostics[0])
	}
	slices.Sort(selected)
	program.SelectedPackages = lean.ArrayFromSlice(selected)
	program.Objects = lean.ArrayFromSlice(objects)
	program.Types = lean.ArrayFromSlice(typeTable)
	program.Expressions = lean.ArrayFromSlice(expressions)
	program.Statements = lean.ArrayFromSlice(statements)
	return program, nil
}

func constantValue(value constant.Value) loaded.Constant {
	if value == nil {
		return loaded.Constant{}
	}
	if value.Kind() == constant.String {
		return loaded.Constant{Present: true, Value: constant.StringVal(value)}
	}
	entry := loaded.Constant{Present: true, Value: value.ExactString()}
	if value.Kind() == constant.Int {
		entry.Integer = true
		entry.Negative = constant.Sign(value) < 0
		entry.MagnitudeBits = constant.BitLen(value)
		if entry.Negative {
			// A negative integer needs one sign bit plus the width of its bitwise complement.
			inverted := constant.UnaryOp(token.XOR, value, 0)
			entry.SignedBits = constant.BitLen(inverted) + 1
		} else {
			entry.SignedBits = entry.MagnitudeBits + 1
		}
	}
	return entry
}

func readType(typ types.Type, typeID func(types.Type) loaded.TypeID, objectID func(types.Object) loaded.ObjectID) loaded.Type {
	entry := loaded.Type{Display: typ.String()}
	switch t := typ.(type) {
	case *types.Basic:
		entry.Kind, entry.Basic = loaded.BasicType, types.Typ[t.Kind()].Name()
	case *types.Alias:
		entry.Kind = loaded.AliasType
		entry.Object = objectID(t.Obj())
		entry.Generic = t.TypeParams().Len() != 0
		entry.Underlying = typeID(types.Unalias(t))
	case *types.Named:
		entry.Kind = loaded.NamedType
		entry.Object = objectID(t.Obj())
		entry.Generic = t.TypeParams().Len() != 0
		entry.PackageScope = t.Obj().Pkg() != nil && t.Obj().Parent() == t.Obj().Pkg().Scope()
		entry.Underlying = typeID(t.Underlying())
		var args []loaded.TypeID
		for arg := range t.TypeArgs().Types() {
			args = append(args, typeID(arg))
		}
		entry.Args = lean.ArrayFromSlice(args)
	case *types.Struct:
		entry.Kind = loaded.StructType
		var fields []loaded.ObjectID
		for field := range t.Fields() {
			fields = append(fields, objectID(field))
		}
		entry.Fields = lean.ArrayFromSlice(fields)
	case *types.Signature:
		entry.Kind = loaded.SignatureType
		entry.Generic = t.TypeParams().Len() != 0
		entry.Variadic = t.Variadic()
		if recv := t.Recv(); recv != nil {
			entry.Receiver = objectID(recv)
			named, ok := types.Unalias(recv.Type()).(*types.Named)
			entry.ValueReceiver = ok && !types.IsInterface(named)
		}
		var params, results []loaded.ObjectID
		for param := range t.Params().Variables() {
			params = append(params, objectID(param))
		}
		for result := range t.Results().Variables() {
			results = append(results, objectID(result))
		}
		entry.Params = lean.ArrayFromSlice(params)
		entry.Results = lean.ArrayFromSlice(results)
	}
	return entry
}

func readDeclarations(p *packages.Package, files []*ast.File, generated *ast.File,
	objectID func(types.Object) loaded.ObjectID, typeID func(types.Type) loaded.TypeID,
	objects *[]loaded.Object, expressions *[]loaded.Expression, statements *[]loaded.Statement,
) lean.Array[loaded.Declaration] {
	var declarations []loaded.Declaration
	add := func(pos token.Pos, obj types.Object) loaded.ObjectID {
		id := objectID(obj)
		declarations = append(declarations, loaded.Declaration{Pos: p.Fset.Position(pos).String(), Object: id})
		return id
	}
	for _, file := range files {
		for _, raw := range file.Decls {
			switch d := raw.(type) {
			case *ast.GenDecl:
				for _, raw := range d.Specs {
					switch spec := raw.(type) {
					case *ast.TypeSpec:
						id := add(spec.Pos(), p.TypesInfo.Defs[spec.Name])
						if file != generated {
							if pos := firstDirective(d.Doc, spec.Doc); pos.IsValid() {
								(*objects)[id].Issue = sourceError(p, pos, "type directives are unsupported; attach laws to functions")
							}
						}
					case *ast.ValueSpec:
						if file != generated {
							for _, name := range spec.Names {
								add(name.Pos(), p.TypesInfo.Defs[name])
							}
						}
					}
				}
			case *ast.FuncDecl:
				if file == generated {
					continue
				}
				id := add(d.Pos(), p.TypesInfo.Defs[d.Name])
				if (*objects)[id].Kind != loaded.FunctionObject {
					continue
				}
				stored := (*objects)[id].Function
				meta := stored.UnwrapOr(loaded.Function{})
				if !stored.IsSome() {
					meta = readDirectives(p, file, d, objectID)
				}
				if d.Body != nil {
					meta.HasBody = true
					meta.Body = readBody(p, d.Body.List, objectID, typeID, expressions, statements)
				}
				(*objects)[id].Function = lean.Some(meta)
			}
		}
	}
	return lean.ArrayFromSlice(declarations)
}
