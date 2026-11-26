package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type checkLocal struct {
	Object    ObjectID
	Package   Package
	Source    Function
	Scope     BindingScope
	Contracts LocalContracts
	Recursive bool
}

func emptyCheckLocal(source Program) checkLocal {
	return checkLocal{Object: 0, Package: source.PackageOrMissing(""), Source: emptyFunction(),
		Scope: emptyBindingScope(), Contracts: LocalContracts{Uses: lean.OrderedMap[ObjectID, bool]{}}, Recursive: false}
}

func (f checkLocal) withScope(scope BindingScope) checkLocal {
	return checkLocal{Object: f.Object, Package: f.Package, Source: f.Source, Scope: scope,
		Contracts: f.Contracts, Recursive: f.Recursive}
}

func (f checkLocal) withContracts(contracts LocalContracts) checkLocal {
	return checkLocal{Object: f.Object, Package: f.Package, Source: f.Source, Scope: f.Scope,
		Contracts: contracts, Recursive: f.Recursive}
}

func (f checkLocal) markingRecursive() checkLocal {
	return checkLocal{Object: f.Object, Package: f.Package, Source: f.Source, Scope: f.Scope,
		Contracts: f.Contracts, Recursive: true}
}

type CheckFunctionStart struct{ Object ObjectID }

type functionPhase uint8

const (
	functionParams functionPhase = iota
	functionParamReady
	functionResultReady
	functionContracts
	functionBodyReady
)

type CheckFunctionWork struct {
	Local       checkLocal
	Signature   Type
	Phase       functionPhase
	Index       uint
	Params      lean.Array[CheckedParameter]
	Result      CheckedType
	ContractIDs lean.Array[ObjectID]
}

func (w CheckFunctionWork) next(phase functionPhase, index uint) CheckFunctionWork {
	return CheckFunctionWork{Local: w.Local, Signature: w.Signature, Phase: phase, Index: index,
		Params: w.Params, Result: w.Result, ContractIDs: w.ContractIDs}
}

func (r checkRun) pushFunction(work CheckFunctionWork) checkRun {
	return r.push(NewCheckTaskCheckFunctionWork(work))
}

func (r checkRun) startFunction(id ObjectID) checkRun {
	p := r.Data.Source
	obj := p.ObjectOrMissing(id)
	entry := r.Data.Calls.FunctionEntry(id, obj)
	if entry.Diagnostic.Code != Valid {
		return r.fail(entry.Diagnostic)
	}
	if entry.Done {
		return r
	}
	src := entry.Source
	sig := p.TypeOrMissing(obj.Type)
	result := p.ObjectOrMissing(sig.Results.Get(0).UnwrapOr(0))
	issue := src.ValidateSignature(sig, result)
	if issue.Code != Valid {
		return r.fail(issue)
	}
	pkg := p.PackageOrMissing(obj.Package)
	local := checkLocal{Object: id, Package: pkg, Source: src, Scope: emptyBindingScope(),
		Contracts: LocalContracts{Uses: lean.OrderedMap[ObjectID, bool]{}}, Recursive: false}
	data := r.Data.discover(pkg.Path).withCalls(r.Data.Calls.Start(id))
	work := CheckFunctionWork{Local: local, Signature: sig, Phase: functionParams, Index: 0,
		Params: lean.Array[CheckedParameter]{}, Result: noCheckedType(), ContractIDs: lean.Array[ObjectID]{}}
	return r.withData(data).pushFunction(work)
}

func signatureParameterCount(sig Type) uint {
	if sig.Receiver != 0 {
		return sig.Params.Size() + 1
	}
	return sig.Params.Size()
}

func signatureParameter(sig Type, index uint) ObjectID {
	if sig.Receiver == 0 {
		return sig.Params.Get(index).UnwrapOr(0)
	}
	if index == 0 {
		return sig.Receiver
	}
	return sig.Params.Get(index - 1).UnwrapOr(0)
}

func (r checkRun) resumeFunction(work CheckFunctionWork) checkRun {
	source := r.Data.Source
	if work.Phase == functionParams {
		if work.Index < signatureParameterCount(work.Signature) {
			param := source.ObjectOrMissing(signatureParameter(work.Signature, work.Index))
			return r.pushFunction(work.next(functionParamReady, work.Index)).scheduleType(work.Local.Package, param.Type, work.Local.Source.Pos)
		}
		result := source.ObjectOrMissing(work.Signature.Results.Get(0).UnwrapOr(0))
		return r.pushFunction(work.next(functionResultReady, 0)).scheduleType(work.Local.Package, result.Type, work.Local.Source.Pos)
	}
	if work.Phase == functionParamReady {
		id := signatureParameter(work.Signature, work.Index)
		param := source.ObjectOrMissing(id)
		binding := work.Local.Scope.Bind(id, param.Name != "_")
		value := CheckedParameter{Type: r.Returned.Type, Binding: binding.ID, Name: param.Name, Unused: param.Name == "_" || param.Name == ""}
		next := CheckFunctionWork{Local: work.Local.withScope(binding.Scope), Signature: work.Signature, Phase: functionParams,
			Index: work.Index + 1, Params: work.Params.Push(value), Result: work.Result, ContractIDs: work.ContractIDs}
		return r.pushFunction(next)
	}
	if work.Phase == functionResultReady {
		issue := work.Local.Source.ValidateFunctionContractMode()
		if issue.Code != Valid {
			return r.fail(issue)
		}
		next := CheckFunctionWork{Local: work.Local, Signature: work.Signature, Phase: functionContracts,
			Index: 0, Params: work.Params, Result: r.Returned.Type, ContractIDs: work.ContractIDs}
		return r.pushFunction(next)
	}
	if work.Phase == functionContracts {
		return r.functionContracts(work)
	}
	return r.finishFunction(work)
}

func (r checkRun) functionContracts(work CheckFunctionWork) checkRun {
	local := work.Local
	if work.Index >= local.Source.Abstract.Size() {
		cursor := BodyCursor{Statements: local.Source.Body, Index: 0, Tail: 0}
		body := emptyBodyState().Visit(cursor)
		return r.pushFunction(work.next(functionBodyReady, 0)).pushBody(startCheckBody(local, body))
	}
	target := local.Source.Abstract.Get(work.Index).UnwrapOr(AbstractCallee{Name: "", Object: 0})
	object := r.Data.Source.ObjectOrMissing(target.Object)
	checked := local.Contracts.CheckContractTarget(local.Object, target, object, local.Source.Pos)
	if checked.Diagnostic.Code != Valid {
		return r.fail(checked.Diagnostic)
	}
	sig := r.Data.Source.CheckContractSignature(object, local.Package.WordBits, local.Source.Pos)
	if sig.Diagnostic.Code != Valid {
		return r.fail(sig.Diagnostic)
	}
	contract := CheckedContractDeclaration{Caller: local.Object, Callee: target.Object, Assumptions: checked.Source.Assumptions, Signature: sig}
	decl := CheckedDeclaration{Kind: CheckedContractDecl, Object: 0, Type: noCheckedType(), Group: lean.Array[ObjectID]{},
		Function: lean.None[CheckedFunction](), Contract: lean.Some(contract)}
	data := r.Data.addDeclaration(local.Package.Path, decl)
	next := CheckFunctionWork{Local: local.withContracts(local.Contracts.Declare(target.Object)), Signature: work.Signature,
		Phase: functionContracts, Index: work.Index + 1, Params: work.Params, Result: work.Result,
		ContractIDs: work.ContractIDs.Push(target.Object)}
	return r.withData(data).pushFunction(next)
}

type lawMatch struct {
	Laws lean.Array[CheckedLaw]
	Name string
}

func matchesLaw(index uint, state lawMatch) lean.FoldControl[lawMatch] {
	fallback := CheckedLaw{Proposition: Proposition{Name: "", Lean: ""}, Caller: 0, Contracts: lean.Array[ObjectID]{}}
	law := state.Laws.Get(index).UnwrapOr(fallback)
	return lean.FoldControl[lawMatch]{State: state, Stop: law.Proposition.Name == state.Name}
}

type appendFunctionLaws struct {
	Laws      lean.Array[CheckedLaw]
	Local     checkLocal
	Contracts lean.Array[ObjectID]
	Issue     Diagnostic
}

func checkFunctionLaw(index uint, state appendFunctionLaws) lean.FoldControl[appendFunctionLaws] {
	law := state.Local.Source.Laws.Get(index).UnwrapOr(Proposition{Name: "", Lean: ""})
	wanted := lawMatch{Laws: state.Laws, Name: law.Name}
	if lean.FoldNUntil(state.Laws.Size(), wanted, matchesLaw).Stop {
		issue := Diagnostic{Code: DuplicatePackageLaw, Pos: state.Local.Source.LawPositions.Get(index).UnwrapOr(""), Detail: law.Name}
		next := appendFunctionLaws{Laws: state.Laws, Local: state.Local, Contracts: state.Contracts, Issue: issue}
		return lean.FoldControl[appendFunctionLaws]{State: next, Stop: true}
	}
	value := CheckedLaw{Proposition: law, Caller: state.Local.Object, Contracts: state.Contracts}
	next := appendFunctionLaws{Laws: state.Laws.Push(value), Local: state.Local, Contracts: state.Contracts, Issue: state.Issue}
	return lean.FoldControl[appendFunctionLaws]{State: next, Stop: false}
}

func (r checkRun) finishFunction(work CheckFunctionWork) checkRun {
	local := r.Returned.Local
	issue := local.Contracts.CheckFunctionFinish(local.Source, local.Recursive)
	if issue.Code != Valid {
		return r.fail(issue)
	}
	pkg := r.Data.packageState(local.Package.Path)
	initial := appendFunctionLaws{Laws: pkg.Laws, Local: local, Contracts: work.ContractIDs, Issue: validDiagnostic()}
	checked := lean.FoldNUntil(local.Source.Laws.Size(), initial, checkFunctionLaw)
	if checked.Stop {
		return r.fail(checked.State.Issue)
	}
	function := CheckedFunction{Body: r.Returned.Body.Nodes, Root: r.Returned.Body.Value, Result: work.Result,
		Params: work.Params, Contracts: work.ContractIDs, Termination: local.Source.Termination}
	decl := CheckedDeclaration{Kind: CheckedFunctionDecl, Object: local.Object, Type: noCheckedType(), Group: lean.Array[ObjectID]{},
		Function: lean.Some(function), Contract: lean.None[CheckedContractDeclaration]()}
	updated := CheckedPackage{Source: pkg.Source, Imports: pkg.Imports, LeanImports: pkg.LeanImports,
		Declarations: pkg.Declarations.Push(decl), Laws: checked.State.Laws, Folds: pkg.Folds}
	data := r.Data.updatePackage(local.Package.Path, updated).withCalls(r.Data.Calls.Finish(local.Object))
	return r.withData(data)
}

type expressionPhase uint8

const (
	expressionAdvance expressionPhase = iota
	expressionTypeReady
	expressionCalleeReady
)

type CheckExpressionWork struct {
	Local   checkLocal
	Walk    ExprWalk
	Phase   expressionPhase
	Request CallRequest
}

func (r checkRun) pushExpression(local checkLocal, walk ExprWalk, phase expressionPhase, request CallRequest) checkRun {
	task := CheckExpressionWork{Local: local, Walk: walk, Phase: phase, Request: request}
	return r.push(NewCheckTaskCheckExpressionWork(task))
}

func (r checkRun) scheduleExpression(local checkLocal, body BodyState, id ExprID) checkRun {
	walk := StartExpression(r.Data.Source, local.Scope, body.Nodes, id)
	return r.pushExpression(local, walk, expressionAdvance, emptyCallRequest())
}

func (r checkRun) resumeExpression(task CheckExpressionWork) checkRun {
	if task.Phase == expressionTypeReady {
		return r.pushExpression(task.Local, task.Walk.WithResolvedType(r.Returned.Type), expressionAdvance, emptyCallRequest())
	}
	if task.Phase == expressionCalleeReady {
		object := r.Data.Source.ObjectOrMissing(task.Request.Target)
		issue := object.ValidateConcreteTarget(task.Request.Pos)
		if issue.Code != Valid {
			return r.fail(issue)
		}
		return r.resumeCall(task.Local, task.Walk, task.Request, false)
	}
	if !task.Walk.Pending() {
		result := checkedReturn{Type: r.Returned.Type, Expr: task.Walk, Body: r.Returned.Body, Local: task.Local}
		return r.withReturn(result)
	}
	next := AdvanceExpression(task.Walk)
	if next.Effect == ExprReject {
		return r.fail(next.Diagnostic)
	}
	if next.Effect == ExprResolveType {
		return r.pushExpression(task.Local, next.Walk, expressionTypeReady, emptyCallRequest()).scheduleType(task.Local.Package, next.Type, next.Pos)
	}
	if next.Effect == ExprResolveCallee {
		return r.checkCall(task.Local, next.Walk, next.Call)
	}
	return r.pushExpression(task.Local, next.Walk, expressionAdvance, emptyCallRequest())
}

func (r checkRun) resumeCall(local checkLocal, walk ExprWalk, request CallRequest, abstract bool) checkRun {
	data := r.Data.addFold(local.Package.Path, request.Fold)
	return r.withData(data).pushExpression(local, walk.WithResolvedCall(request, abstract), expressionAdvance, emptyCallRequest())
}

func (r checkRun) checkCall(local checkLocal, walk ExprWalk, request CallRequest) checkRun {
	if request.Fold == 0 && request.Target == local.Object && local.Source.Termination != "" {
		return r.resumeCall(local.markingRecursive(), walk, request, false)
	}
	use := local.Contracts.Use(request.Target)
	if use.Found {
		return r.resumeCall(local.withContracts(use.Contracts), walk, request, true)
	}
	obj := r.Data.Source.ObjectOrMissing(request.Target)
	visible := obj.ValidateConcreteCall(local.Package.Path, request.Pos)
	if visible.Code != Valid {
		return r.fail(visible)
	}
	target := r.Data.Source.PackageOrMissing(obj.Package)
	issue := local.Package.ValidateDependency(target, obj.Package, request.Pos)
	if issue.Code != Valid {
		return r.fail(issue)
	}
	return r.visitCallee(local, walk, request, obj)
}

func (r checkRun) visitCallee(local checkLocal, walk ExprWalk, request CallRequest, obj Object) checkRun {
	issue := r.Data.Calls.ValidateCallEdge(request.Target, obj, request.Pos)
	if issue.Code != Valid {
		return r.fail(issue)
	}
	if obj.Package != local.Package.Path {
		data := r.Data.dependency(local.Package.Path, obj.Package)
		pending := r.withData(data).pushExpression(local, walk, expressionCalleeReady, request)
		return pending.push(NewCheckTaskCheckFunctionStart(CheckFunctionStart{Object: request.Target}))
	}
	pending := r.pushExpression(local, walk, expressionCalleeReady, request)
	return pending.push(NewCheckTaskCheckFunctionStart(CheckFunctionStart{Object: request.Target}))
}
