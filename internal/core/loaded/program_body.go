package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type bodyPhase uint8

const (
	bodyAdvance bodyPhase = iota
	bodyReturnReady
	bodyIfReady
	bodyMatchTypeReady
	bodyMatchValueReady
	bodyVarTypeReady
	bodyBindings
	bodyBindingExprReady
	bodyBindingTypeReady
)

type bindingWork struct {
	Names   lean.Array[Binding]
	Exprs   lean.Array[ExprID]
	Checked lean.Array[CheckedLetBinding]
	Index   uint
}

func emptyBindingWork() bindingWork {
	return bindingWork{Names: lean.Array[Binding]{}, Exprs: lean.Array[ExprID]{},
		Checked: lean.Array[CheckedLetBinding]{}, Index: 0}
}

type CheckBodyWork struct {
	Local     checkLocal
	Body      BodyState
	Phase     bodyPhase
	Suffix    BodyCursor
	Statement Statement
	Bindings  bindingWork
}

func missingStatement() Statement {
	return Statement{Pos: "", Form: NewStmtFormUnsupportedStmt(UnsupportedStmt{Syntax: ""})}
}

func startCheckBody(local checkLocal, body BodyState) CheckBodyWork {
	return CheckBodyWork{Local: local, Body: body, Phase: bodyAdvance, Suffix: emptyCursor(),
		Statement: missingStatement(), Bindings: emptyBindingWork()}
}

func (w CheckBodyWork) withPhase(phase bodyPhase) CheckBodyWork {
	return CheckBodyWork{Local: w.Local, Body: w.Body, Phase: phase, Suffix: w.Suffix,
		Statement: w.Statement, Bindings: w.Bindings}
}

func (w CheckBodyWork) withBody(local checkLocal, body BodyState) CheckBodyWork {
	return CheckBodyWork{Local: local, Body: body, Phase: w.Phase, Suffix: w.Suffix,
		Statement: w.Statement, Bindings: w.Bindings}
}

func (r checkRun) pushBody(task CheckBodyWork) checkRun {
	return r.push(NewCheckTaskCheckBodyWork(task))
}

func (r checkRun) resumeBody(task CheckBodyWork) checkRun {
	if task.Phase == bodyAdvance {
		return r.advanceBodyTask(task)
	}
	if task.Phase == bodyReturnReady {
		body := task.Body.WithCheckedExpression(r.Returned.Expr)
		return r.pushBody(startCheckBody(r.Returned.Local, body))
	}
	if task.Phase == bodyBindings {
		return r.visitBinding(task)
	}
	if task.Phase == bodyBindingExprReady {
		return r.checkBindingType(task)
	}
	if task.Phase == bodyBindingTypeReady {
		return r.finishBinding(task)
	}
	return r.resumeBodyStatement(task)
}

func (r checkRun) advanceBodyTask(task CheckBodyWork) checkRun {
	if !task.Body.Frames.IsSome() {
		returned := checkedReturn{Type: r.Returned.Type, Expr: r.Returned.Expr, Body: task.Body, Local: task.Local}
		return r.withReturn(returned)
	}
	frame := AdvanceBody(task.Body)
	next := task.withBody(task.Local, frame.State)
	if frame.Effect == BodyVisitStatement {
		id := frame.Cursor.Statements.Get(frame.Cursor.Index).UnwrapOr(0)
		statement := r.Data.Source.LookupStatement(id).UnwrapOr(missingStatement())
		suffix := BodyCursor{Statements: frame.Cursor.Statements, Index: frame.Cursor.Index + 1, Tail: frame.Cursor.Tail}
		work := CheckBodyWork{Local: task.Local, Body: frame.State, Phase: bodyAdvance, Suffix: suffix,
			Statement: statement, Bindings: emptyBindingWork()}
		return r.beginBodyStatement(work)
	}
	if frame.Effect == BodyVisitMatchCase {
		return r.checkMatchCase(next, frame.Match)
	}
	if frame.Effect == BodyCompleteMatchCase {
		clause := next.Body.Match(frame.Match).Clause().UnwrapOr(emptySwitchClause())
		local := next.Local.withScope(next.Local.Scope.Remove(clause.Binding))
		variant := r.Data.Source.ObjectOrMissing(clause.Variant)
		return r.pushBody(startCheckBody(local, next.Body.EndCase(frame.Match, variant.Name)))
	}
	if frame.Effect == BodyMissingReturn {
		return r.withFailure(failedCheck(MissingBodyReturn, task.Local.Source.Pos, ""))
	}
	if frame.Effect == BodyUnreachableSuffix {
		id := frame.Cursor.Statements.Get(frame.Cursor.Index).UnwrapOr(0)
		statement := r.Data.Source.LookupStatement(id).UnwrapOr(missingStatement())
		return r.withFailure(failedCheck(UnreachableBodySuffix, statement.Pos, ""))
	}
	return r.pushBody(next)
}

func emptySwitchClause() SwitchClause {
	return SwitchClause{Pos: "", Count: 0, Variant: 0, Binding: 0, Body: lean.Array[StmtID]{}}
}

func (r checkRun) checkMatchCase(task CheckBodyWork, id uint) checkRun {
	match := task.Body.Match(id)
	option := match.Clause()
	if !option.IsSome() {
		missing := match.Coverage.MissingCase()
		if missing != 0 {
			name := r.Data.Source.ObjectOrMissing(missing).Name
			return r.withFailure(failedCheck(NonExhaustiveMatch, match.Pos, name))
		}
		return r.pushBody(startCheckBody(task.Local, task.Body.FinishMatch(match)))
	}
	clause := option.UnwrapOr(emptySwitchClause())
	issue := match.Coverage.ValidateCase(clause)
	if issue.Code != Valid {
		return r.fail(issue)
	}
	if clause.Binding == 0 {
		return r.pushBody(startCheckBody(task.Local, task.Body.BeginCase(id, clause, -1)))
	}
	obj := r.Data.Source.ObjectOrMissing(clause.Binding)
	binding := task.Local.Scope.Bind(clause.Binding, obj.Name != "_")
	local := task.Local.withScope(binding.Scope)
	return r.pushBody(startCheckBody(local, task.Body.BeginCase(id, clause, binding.ID)))
}

func (r checkRun) beginBodyStatement(task CheckBodyWork) checkRun {
	statement := task.Statement
	issue := statement.Validate()
	if issue.Code != Valid {
		return r.fail(issue)
	}
	switch form := statement.Form.Case().(type) {
	case ReturnStmt:
		checked := form.ValidatePosition(statement.Pos, !task.Suffix.HasStatements())
		if checked.Code != Valid {
			return r.fail(checked)
		}
		return r.pushBody(task.withPhase(bodyReturnReady)).scheduleExpression(task.Local, task.Body, form.Values.Get(0).UnwrapOr(0))
	case IfStmt:
		return r.pushBody(task.withPhase(bodyIfReady)).scheduleExpression(task.Local, task.Body, form.Condition)
	case SwitchStmt:
		method := r.Data.Source.ObjectOrMissing(form.CaseMethod)
		checked := form.ValidateCaseMethod(method, statement.Pos)
		if checked.Code != Valid {
			return r.fail(checked)
		}
		obj := r.Data.Source.ObjectOrMissing(method.EnumCase)
		return r.pushBody(task.withPhase(bodyMatchTypeReady)).scheduleType(task.Local.Package, obj.Type, statement.Pos)
	case ShortDecl:
		return r.startBindingChecks(task, form.Names, form.Values)
	case VarDecl:
		if form.ZeroType != 0 {
			return r.pushBody(task.withPhase(bodyVarTypeReady)).scheduleType(task.Local.Package, form.ZeroType, form.ZeroTypePos)
		}
		return r.startBindingChecks(task, form.Names, form.Values)
	case UnsupportedStmt:
		return r
	case LoopStmt:
		return r
	}
	return r
}

func (r checkRun) resumeBodyStatement(task CheckBodyWork) checkRun {
	switch form := task.Statement.Form.Case().(type) {
	case IfStmt:
		return r.finishIf(task, form)
	case SwitchStmt:
		if task.Phase == bodyMatchTypeReady {
			return r.pushBody(task.withPhase(bodyMatchValueReady)).scheduleExpression(task.Local, task.Body, form.Receiver)
		}
		return r.finishSwitch(task, form)
	case VarDecl:
		if r.Returned.Type.Kind == EnumShape {
			return r.zeroBinding(task, form.Names.Get(0).UnwrapOr(emptyLocalBinding()))
		}
		return r.startBindingChecks(task, form.Names, form.Values)
	case UnsupportedStmt:
		return r
	case ReturnStmt:
		return r
	case LoopStmt:
		return r
	case ShortDecl:
		return r
	}
	return r
}

func (r checkRun) finishIf(task CheckBodyWork, form IfStmt) checkRun {
	source := r.Data.Source
	join := !source.EndsWithReturn(form.Then) && !source.EndsWithReturn(form.Else)
	body := task.Body.WithCheckedExpression(r.Returned.Expr)
	local := r.Returned.Local
	tail := BodyTail{Suffix: task.Suffix, Join: local.Scope.Next, Jump: join, Used: false, Value: 0}
	pending := body.AddTail(tail)
	then := BodyCursor{Statements: form.Then, Index: 0, Tail: pending.Tails.Size()}
	other := BodyCursor{Statements: form.Else, Index: 0, Tail: pending.Tails.Size()}
	frame := BodyFrame{Kind: CompleteThen, Cursor: other, Tail: pending.Tails.Size(), Match: 0,
		Condition: body.Value, Yes: 0, Branch: 0, Bindings: lean.Array[CheckedLetBinding]{}}
	next := pending.Push(frame).Visit(then)
	if join {
		return r.pushBody(startCheckBody(local.withScope(local.Scope.ReserveID().Scope), next))
	}
	return r.pushBody(startCheckBody(local, next))
}

func (r checkRun) finishSwitch(task CheckBodyWork, form SwitchStmt) checkRun {
	source := r.Data.Source
	method := source.ObjectOrMissing(form.CaseMethod)
	obj := source.ObjectOrMissing(method.EnumCase)
	enum := obj.Enum.UnwrapOr(Enum{Payloads: lean.Array[ObjectID]{}, Default: ""})
	local := r.Returned.Local
	reserved := local.Scope.ReserveID()
	tail := BodyTail{Suffix: task.Suffix, Join: reserved.ID, Jump: true, Used: false, Value: 0}
	body := task.Body.WithCheckedExpression(r.Returned.Expr).AddTail(tail)
	match := body.BeginMatch(task.Statement.Pos, body.Value, form.Cases, enum.Payloads, body.Tails.Size())
	return r.pushBody(startCheckBody(local.withScope(reserved.Scope), match))
}

func emptyLocalBinding() Binding {
	return Binding{Pos: "", Object: 0, Identifier: false}
}

func (r checkRun) zeroBinding(task CheckBodyWork, name Binding) checkRun {
	obj := r.Data.Source.ObjectOrMissing(name.Object)
	binding := task.Local.Scope.Bind(name.Object, obj.Name != "_")
	body := task.Body.AppendZero(r.Returned.Type)
	item := CheckedLetBinding{Binding: binding.ID, Value: body.Value}
	return r.scheduleBindings(task.Local.withScope(binding.Scope), body, task.Suffix, lean.Array[CheckedLetBinding]{}.Push(item))
}

func (r checkRun) scheduleBindings(local checkLocal, body BodyState, suffix BodyCursor, bindings lean.Array[CheckedLetBinding]) checkRun {
	frame := BodyFrame{Kind: WrapBindings, Cursor: emptyCursor(), Tail: 0, Match: 0,
		Condition: 0, Yes: 0, Branch: 0, Bindings: bindings}
	return r.pushBody(startCheckBody(local, body.Push(frame).Visit(suffix)))
}

func (r checkRun) startBindingChecks(task CheckBodyWork, names lean.Array[Binding], exprs lean.Array[ExprID]) checkRun {
	if names.Size() != exprs.Size() {
		return r.withFailure(failedCheck(MissingInitializers, names.Get(0).UnwrapOr(emptyLocalBinding()).Pos, ""))
	}
	bindings := bindingWork{Names: names, Exprs: exprs, Checked: lean.Array[CheckedLetBinding]{}, Index: 0}
	next := CheckBodyWork{Local: task.Local, Body: task.Body, Phase: bodyBindings, Suffix: task.Suffix,
		Statement: task.Statement, Bindings: bindings}
	return r.pushBody(next)
}

func (r checkRun) visitBinding(task CheckBodyWork) checkRun {
	bindings := task.Bindings
	if bindings.Index >= bindings.Names.Size() {
		return r.scheduleBindings(task.Local, task.Body, task.Suffix, bindings.Checked)
	}
	name := bindings.Names.Get(bindings.Index).UnwrapOr(emptyLocalBinding())
	if r.Data.Source.ObjectOrMissing(name.Object).Kind != Variable {
		return r.withFailure(failedCheck(ReassignedBinding, name.Pos, ""))
	}
	expr := bindings.Exprs.Get(bindings.Index).UnwrapOr(0)
	return r.pushBody(task.withPhase(bodyBindingExprReady)).scheduleExpression(task.Local, task.Body, expr)
}

func (r checkRun) checkBindingType(task CheckBodyWork) checkRun {
	name := task.Bindings.Names.Get(task.Bindings.Index).UnwrapOr(emptyLocalBinding())
	obj := r.Data.Source.ObjectOrMissing(name.Object)
	next := task.withBody(r.Returned.Local, task.Body.WithCheckedExpression(r.Returned.Expr))
	return r.pushBody(next.withPhase(bodyBindingTypeReady)).scheduleType(task.Local.Package, obj.Type, name.Pos)
}

func (r checkRun) finishBinding(task CheckBodyWork) checkRun {
	state := task.Bindings
	name := state.Names.Get(state.Index).UnwrapOr(emptyLocalBinding())
	obj := r.Data.Source.ObjectOrMissing(name.Object)
	allocated := task.Local.Scope.Bind(name.Object, obj.Name != "_")
	value := CheckedLetBinding{Binding: allocated.ID, Value: task.Body.Value}
	bindings := bindingWork{Names: state.Names, Exprs: state.Exprs, Checked: state.Checked.Push(value), Index: state.Index + 1}
	next := CheckBodyWork{Local: task.Local.withScope(allocated.Scope), Body: task.Body, Phase: bodyBindings,
		Suffix: task.Suffix, Statement: task.Statement, Bindings: bindings}
	return r.pushBody(next)
}
