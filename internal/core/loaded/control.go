package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type returnWalk struct {
	Program  Program
	Pending  lean.Array[StmtID]
	Rejected bool
}

func lastStatement(block lean.Array[StmtID]) StmtID {
	if block.Size() == 0 {
		return 0
	}
	return block.Get(block.Size() - 1).UnwrapOr(0)
}

func rejectReturnWalk(program Program) lean.FoldControl[returnWalk] {
	return lean.FoldControl[returnWalk]{State: returnWalk{
		Program: program, Pending: lean.Array[StmtID]{}, Rejected: true,
	}, Stop: true}
}

func stepReturnWalk(_ uint, walk returnWalk) lean.FoldControl[returnWalk] {
	if walk.Pending.Size() == 0 {
		return lean.FoldControl[returnWalk]{State: walk, Stop: true}
	}
	id := lastStatement(walk.Pending)
	rest := walk.Pending.Pop()
	missing := Statement{Pos: "", Form: NewStmtFormUnsupportedStmt(UnsupportedStmt{Syntax: ""})}
	statement := walk.Program.LookupStatement(id).UnwrapOr(missing)
	switch form := statement.Form.Case().(type) {
	case ReturnStmt:
		return lean.FoldControl[returnWalk]{State: returnWalk{Program: walk.Program, Pending: rest, Rejected: false}, Stop: rest.Size() == 0}
	case IfStmt:
		if form.Then.Size() == 0 || form.Else.Size() == 0 {
			return rejectReturnWalk(walk.Program)
		}
		next := rest.Push(lastStatement(form.Else)).Push(lastStatement(form.Then))
		return lean.FoldControl[returnWalk]{State: returnWalk{Program: walk.Program, Pending: next, Rejected: false}, Stop: false}
	case UnsupportedStmt:
		return rejectReturnWalk(walk.Program)
	case SwitchStmt:
		return rejectReturnWalk(walk.Program)
	case LoopStmt:
		return rejectReturnWalk(walk.Program)
	case ShortDecl:
		return rejectReturnWalk(walk.Program)
	case VarDecl:
		return rejectReturnWalk(walk.Program)
	}
	return rejectReturnWalk(walk.Program)
}

// EndsWithReturn reports whether the last statement is a return or an if
// whose two branches end with returns. Loader-built blocks own their syntax
// occurrences, so following each terminal branch visits each statement once.
//
//golean:export
func (p Program) EndsWithReturn(block lean.Array[StmtID]) bool {
	if block.Size() == 0 {
		return false
	}
	initial := returnWalk{Program: p, Pending: lean.Array[StmtID]{}.Push(lastStatement(block)), Rejected: false}
	result := lean.FoldNUntil(p.Statements.Size(), initial, stepReturnWalk)
	return result.Stop && !result.State.Rejected
}
