package load

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
	"golang.org/x/tools/go/packages"
)

func readBody(p *packages.Package, body []ast.Stmt, objectID func(types.Object) loaded.ObjectID, typeID func(types.Type) loaded.TypeID,
	expressions *[]loaded.Expression, statements *[]loaded.Statement,
) lean.Array[loaded.StmtID] {
	position := func(pos token.Pos) string { return p.Fset.Position(pos).String() }
	info := p.TypesInfo
	selection := func(sel *types.Selection) loaded.Selection {
		if sel == nil {
			return loaded.Selection{}
		}
		kinds := [...]loaded.SelectionKind{types.FieldVal: loaded.FieldValue, types.MethodVal: loaded.MethodValue, types.MethodExpr: loaded.MethodExpression}
		return loaded.Selection{Kind: kinds[sel.Kind()], Receiver: typeID(sel.Recv()),
			Object: objectID(sel.Obj()), Direct: !sel.Indirect() && len(sel.Index()) == 1}
	}
	var expr func(ast.Expr) loaded.ExprID
	exprs := func(nodes []ast.Expr) lean.Array[loaded.ExprID] {
		ids := make([]loaded.ExprID, 0, len(nodes))
		for _, node := range nodes {
			ids = append(ids, expr(node))
		}
		return lean.ArrayFromSlice(ids)
	}
	expr = func(node ast.Expr) loaded.ExprID {
		if node == nil {
			return 0
		}
		entry := loaded.Expression{Pos: position(node.Pos()), Syntax: fmt.Sprintf("%T", node), Type: typeID(info.TypeOf(node)), Constant: constantValue(info.Types[node].Value)}
		switch e := node.(type) {
		case *ast.ParenExpr:
			entry.Form = loaded.NewExprFormParenthesized(loaded.Parenthesized{Inner: expr(e.X)})
		case *ast.Ident:
			entry.Form = loaded.NewExprFormIdentifier(loaded.Identifier{Name: e.Name, Object: objectID(info.Uses[e])})
		case *ast.UnaryExpr:
			entry.Form = loaded.NewExprFormUnaryExpr(loaded.UnaryExpr{Operator: e.Op.String(), Operand: expr(e.X)})
		case *ast.BinaryExpr:
			entry.Form = loaded.NewExprFormBinaryExpr(loaded.BinaryExpr{Operator: e.Op.String(), Left: expr(e.X), Right: expr(e.Y)})
		case *ast.SelectorExpr:
			entry.Form = loaded.NewExprFormSelectorExpr(loaded.SelectorExpr{Base: expr(e.X), Object: objectID(info.Uses[e.Sel]), Selection: selection(info.Selections[e])})
		case *ast.CompositeLit:
			entry.Form = loaded.NewExprFormCompositeExpr(loaded.CompositeExpr{Elements: exprs(e.Elts)})
		case *ast.KeyValueExpr:
			keyed := loaded.KeyedExpr{Value: expr(e.Value)}
			if key, ok := e.Key.(*ast.Ident); ok {
				keyed.Name = key.Name
			}
			entry.Form = loaded.NewExprFormKeyedExpr(keyed)
		case *ast.CallExpr:
			call := loaded.CallExpr{Args: exprs(e.Args), Ellipsis: e.Ellipsis.IsValid(), Conversion: info.Types[e.Fun].IsType()}
			switch target := callBase(e.Fun).(type) {
			case *ast.Ident:
				call.Object = objectID(info.Uses[target])
			case *ast.SelectorExpr:
				call.Object, call.Selection = objectID(info.Uses[target.Sel]), selection(info.Selections[target])
				if call.Selection.Kind == loaded.MethodValue {
					call.Receiver = expr(target.X)
				}
			}
			entry.Form = loaded.NewExprFormCallExpr(call)
		}
		id := loaded.ExprID(len(*expressions))
		*expressions = append(*expressions, entry)
		return id
	}
	binding := func(node ast.Expr) loaded.Binding {
		id, ok := node.(*ast.Ident)
		entry := loaded.Binding{Pos: position(node.Pos()), Identifier: ok}
		if ok {
			entry.Object = objectID(info.Defs[id])
		}
		return entry
	}
	var stmt func(ast.Stmt) loaded.StmtID
	block := func(nodes []ast.Stmt) lean.Array[loaded.StmtID] {
		ids := make([]loaded.StmtID, 0, len(nodes))
		for _, node := range nodes {
			ids = append(ids, stmt(node))
		}
		return lean.ArrayFromSlice(ids)
	}
	stmt = func(node ast.Stmt) loaded.StmtID {
		entry := loaded.Statement{Pos: position(node.Pos())}
		switch s := node.(type) {
		case *ast.ReturnStmt:
			entry.Form = loaded.NewStmtFormReturnStmt(loaded.ReturnStmt{Values: exprs(s.Results)})
		case *ast.IfStmt:
			branch := loaded.IfStmt{HasInitializer: s.Init != nil, Condition: expr(s.Cond), Then: block(s.Body.List)}
			switch other := s.Else.(type) {
			case *ast.IfStmt:
				branch.Else = block([]ast.Stmt{other})
			case *ast.BlockStmt:
				branch.Else = block(other.List)
			}
			entry.Form = loaded.NewStmtFormIfStmt(branch)
		case *ast.TypeSwitchStmt:
			match := loaded.SwitchStmt{}
			if sel := caseSelector(s); sel != nil {
				target := selection(info.Selections[sel])
				if target.Kind == loaded.MethodValue && target.Direct {
					match.CaseMethod, match.Receiver = target.Object, expr(sel.X)
				}
			}
			var cases []loaded.SwitchClause
			for _, node := range s.Body.List {
				clause := node.(*ast.CaseClause)
				arm := loaded.SwitchClause{Pos: position(clause.Pos()), Count: len(clause.List), Body: block(clause.Body)}
				arm.Binding = objectID(info.Implicits[clause])
				if arm.Count == 1 {
					if typ, ok := types.Unalias(info.TypeOf(clause.List[0])).(*types.Named); ok {
						arm.Variant = objectID(typ.Obj())
					}
				}
				cases = append(cases, arm)
			}
			match.Cases = lean.ArrayFromSlice(cases)
			entry.Form = loaded.NewStmtFormSwitchStmt(match)
		case *ast.ForStmt, *ast.RangeStmt:
			entry.Form = loaded.NewStmtFormLoopStmt(loaded.LoopStmt{})
		case *ast.AssignStmt:
			decl := loaded.ShortDecl{ValidForm: s.Tok == token.DEFINE && len(s.Lhs) == len(s.Rhs)}
			if decl.ValidForm {
				var names []loaded.Binding
				for _, name := range s.Lhs {
					names = append(names, binding(name))
				}
				decl.Names, decl.Values = lean.ArrayFromSlice(names), exprs(s.Rhs)
			}
			entry.Form = loaded.NewStmtFormShortDecl(decl)
		case *ast.DeclStmt:
			d, ok := s.Decl.(*ast.GenDecl)
			decl := loaded.VarDecl{ValidForm: ok && d.Tok == token.VAR && len(d.Specs) == 1}
			if decl.ValidForm {
				v := d.Specs[0].(*ast.ValueSpec)
				var names []loaded.Binding
				for _, name := range v.Names {
					names = append(names, binding(name))
				}
				decl.Names, decl.Values = lean.ArrayFromSlice(names), exprs(v.Values)
				if len(v.Values) == 0 && len(v.Names) == 1 {
					decl.ZeroType, decl.ZeroTypePos = typeID(info.Defs[v.Names[0]].Type()), position(v.Pos())
				}
			}
			entry.Form = loaded.NewStmtFormVarDecl(decl)
		default:
			entry.Form = loaded.NewStmtFormUnsupportedStmt(loaded.UnsupportedStmt{Syntax: fmt.Sprintf("%T", node)})
		}
		id := loaded.StmtID(len(*statements))
		*statements = append(*statements, entry)
		return id
	}
	return block(body)
}

func caseSelector(stmt *ast.TypeSwitchStmt) *ast.SelectorExpr {
	if stmt.Init != nil {
		return nil
	}
	var expr ast.Expr
	switch assign := stmt.Assign.(type) {
	case *ast.AssignStmt:
		if assign.Tok != token.DEFINE || len(assign.Rhs) != 1 {
			return nil
		}
		expr = assign.Rhs[0]
	case *ast.ExprStmt:
		expr = assign.X
	}
	assertion, ok := expr.(*ast.TypeAssertExpr)
	if !ok {
		return nil
	}
	call, ok := assertion.X.(*ast.CallExpr)
	if !ok || len(call.Args) != 0 {
		return nil
	}
	selector, _ := call.Fun.(*ast.SelectorExpr)
	return selector
}

func callBase(e ast.Expr) ast.Expr {
	for {
		switch node := e.(type) {
		case *ast.ParenExpr:
			e = node.X
		case *ast.IndexExpr:
			e = node.X
		case *ast.IndexListExpr:
			e = node.X
		default:
			return e
		}
	}
}
