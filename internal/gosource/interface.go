package gosource

import (
	"go/ast"
	"go/token"
	"go/types"
	"strings"

	"golang.org/x/tools/go/packages"
)

// InterfaceDoc holds comment groups in interface declaration order.
type InterfaceDoc struct {
	fset   *token.FileSet
	groups []*ast.CommentGroup
}

func interfaceDocs(loaded []*packages.Package) map[*types.TypeName]InterfaceDoc {
	docs := make(map[*types.TypeName]InterfaceDoc)
	packages.Visit(loaded, nil, func(pkg *packages.Package) {
		for _, file := range pkg.Syntax {
			for _, decl := range file.Decls {
				group, ok := decl.(*ast.GenDecl)
				if !ok || group.Tok != token.TYPE {
					continue
				}
				for _, spec := range group.Specs {
					spec := spec.(*ast.TypeSpec)
					iface, ok := spec.Type.(*ast.InterfaceType)
					if !ok || spec.Assign.IsValid() {
						continue
					}
					doc := InterfaceDoc{fset: pkg.Fset}
					if !group.Lparen.IsValid() {
						doc.groups = append(doc.groups, group.Doc)
					}
					doc.groups = append(doc.groups, spec.Doc)
					for _, field := range iface.Methods.List {
						doc.groups = append(doc.groups, field.Doc)
					}
					docs[pkg.TypesInfo.Defs[spec.Name].(*types.TypeName)] = doc
				}
			}
		}
	})
	return docs
}

// Laws decodes the contract when its interface is reached by verification.
func (doc InterfaceDoc) Laws() ([]string, error) {
	var laws []string
	for _, group := range doc.groups {
		if group == nil {
			continue
		}
		for _, comment := range group.List {
			line, isLine := strings.CutPrefix(comment.Text, "//")
			if !isLine {
				continue
			}
			fields := strings.Fields(line)
			if len(fields) == 0 {
				continue
			}
			switch fields[0] {
			case "golean:start", "golean:end", "golean:law":
				return nil, doc.error(comment.Pos(), "legacy contract marker; use //golean:assume for each law")
			case "golean:assume":
				law := strings.TrimSpace(strings.TrimPrefix(strings.TrimSpace(line), "golean:assume"))
				name, proposition, valid := strings.Cut(law, ":")
				if !valid || len(strings.Fields(name)) != 1 || strings.TrimSpace(proposition) == "" {
					return nil, doc.error(comment.Pos(), "expected //golean:assume <name> : <Lean proposition>")
				}
				laws = append(laws, law)
			}
		}
	}
	return laws, nil
}

func (doc InterfaceDoc) error(pos token.Pos, message string) error {
	return packages.Error{Pos: doc.fset.Position(pos).String(), Msg: message}
}
