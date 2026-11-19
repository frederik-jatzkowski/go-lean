package gosource

import (
	"go/ast"
	"go/token"
	"go/types"
	"regexp"
	"slices"
	"strings"
	"unicode/utf8"

	"golang.org/x/tools/go/packages"
)

type LeanImports struct {
	Verify []string
	Assume []string
}

// Restrict the payload to a Lean module name, including quoted name segments.
const leanModuleSegment = `(?:[\p{L}_][\p{L}\p{M}\p{N}_']*|«[^«»\s]+»)`

var leanModulePattern = regexp.MustCompile(`^` + leanModuleSegment + `(?:\.` + leanModuleSegment + `)*$`)
var leanSegmentPattern = regexp.MustCompile(leanModuleSegment)

func quoteLeanModule(module string) string {
	return leanSegmentPattern.ReplaceAllStringFunc(module, func(segment string) string {
		if strings.HasPrefix(segment, "«") {
			return segment
		}
		return "«" + segment + "»"
	})
}

func packageLeanImports(loaded []*packages.Package) (map[string]LeanImports, error) {
	result := make(map[string]LeanImports)
	var err error
	packages.Visit(loaded, func(pkg *packages.Package) bool {
		var imports LeanImports
		for _, file := range pkg.Syntax {
			if file.Doc == nil {
				continue
			}
			for _, comment := range file.Doc.List {
				directive, payload := directiveParts(comment.Text)
				var modules *[]string
				switch directive {
				case "//golean:verify:import":
					modules = &imports.Verify
				case "//golean:assume:import":
					modules = &imports.Assume
				default:
					continue
				}
				if !leanModulePattern.MatchString(payload) {
					err = directiveError(pkg.Fset.PositionFor(comment.Pos(), false), "expected %s <Lean.Module>", directive)
					return false
				}
				*modules = append(*modules, quoteLeanModule(payload))
			}
		}
		if len(imports.Verify)+len(imports.Assume) != 0 {
			slices.Sort(imports.Verify)
			slices.Sort(imports.Assume)
			imports.Verify = slices.Compact(imports.Verify)
			imports.Assume = slices.Compact(imports.Assume)
			result[pkg.PkgPath] = imports
		}
		return err == nil
	}, nil)
	return result, err
}

func directiveParts(line string) (directive, payload string) {
	fields := strings.Fields(line)
	if len(fields) == 0 {
		return "", ""
	}
	return fields[0], strings.TrimSpace(strings.TrimPrefix(line, fields[0]))
}

func scopedLaws(pkg *packages.Package, file *ast.File, roots []selectedRoot) ([]Law, error) {
	allowed := make(map[*ast.CommentGroup]bool)
	concrete := make(map[*ast.CommentGroup]bool)
	names := make(map[string]token.Position)
	for _, root := range roots {
		for _, law := range root.laws {
			names[law.Name] = law.Position
		}
	}
	for _, decl := range file.Decls {
		switch decl := decl.(type) {
		case *ast.FuncDecl:
			allowed[decl.Doc] = true
		case *ast.GenDecl:
			if decl.Tok != token.TYPE {
				continue
			}
			for _, entry := range decl.Specs {
				spec := entry.(*ast.TypeSpec)
				_, iface := spec.Type.(*ast.InterfaceType)
				obj, _ := pkg.TypesInfo.Defs[spec.Name].(*types.TypeName)
				if obj != nil {
					_, iface = obj.Type().Underlying().(*types.Interface)
				}
				if iface || spec.Assign.IsValid() {
					continue
				}
				if spec.Doc != nil {
					concrete[spec.Doc] = true
				}
				if len(decl.Specs) == 1 && decl.Doc != nil && !decl.Lparen.IsValid() {
					concrete[decl.Doc] = true
				}
			}
		}
	}
	var laws []Law
	for _, group := range file.Comments {
		var continuation *Law
		for _, comment := range group.List {
			kind, payload := directiveParts(comment.Text)
			pos := pkg.Fset.PositionFor(comment.Pos(), false)
			switch kind {
			case "//golean:verify:import", "//golean:assume:import":
				if group != file.Doc {
					return nil, directiveError(pos, "%s belongs in a package doc comment", kind)
				}
			case "//golean:verify", "//golean:verify+":
				if allowed[group] {
					continue
				}
				if group != file.Doc && !concrete[group] {
					return nil, directiveError(pos, "%s requires a function, method, concrete type, or package doc comment", kind)
				}
				if kind == "//golean:verify+" {
					if continuation == nil || payload == "" || pos.Line != continuation.Position.Line+strings.Count(continuation.Proposition, "\n")+1 {
						return nil, directiveError(pos, "expected a nonempty continuation immediately after a named //golean:verify law")
					}
					remainder := strings.TrimPrefix(comment.Text, kind)
					_, separator := utf8.DecodeRuneInString(remainder)
					continuation.Proposition += "\n" + remainder[separator:]
					continue
				}
				name, proposition, _ := strings.Cut(payload, ":")
				name, proposition = strings.TrimSpace(name), strings.TrimSpace(proposition)
				if !token.IsIdentifier(name) || name == "_" || proposition == "" {
					return nil, directiveError(pos, "expected //golean:verify <name> : <Lean proposition>")
				}
				if previous, exists := names[name]; exists {
					if previous.Line > pos.Line {
						pos = previous
					}
					return nil, directiveError(pos, "duplicate verification law %q", name)
				}
				names[name] = pos
				laws = append(laws, Law{Name: name, Proposition: proposition, Position: pos})
				continuation = &laws[len(laws)-1]
				continue
			}
			continuation = nil
		}
	}
	return laws, nil
}
