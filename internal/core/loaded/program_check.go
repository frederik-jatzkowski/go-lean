package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type CheckFailure struct {
	Diagnostic Diagnostic
	Extra      string
	Cycle      lean.Array[string]
}

type CheckResult struct {
	Program  CheckedProgram
	Failure  CheckFailure
	Complete bool
}

type checkPackages struct {
	Values   lean.OrderedMap[string, CheckedPackage]
	Paths    lean.Array[string]
	Schedule PackageSchedule
}

type checkData struct {
	Source   Program
	Packages checkPackages
	Calls    CallGraph
	Seen     lean.OrderedSet[ObjectID]
	Named    lean.OrderedMap[ObjectID, CheckedTypeDeclaration]
}

type checkStack struct {
	Task CheckTask
	Rest lean.Box[checkStack]
}

type checkedReturn struct {
	Type  CheckedType
	Expr  ExprWalk
	Body  BodyState
	Local checkLocal
}

type checkRun struct {
	Data     checkData
	Stack    lean.Box[checkStack]
	Returned checkedReturn
	Failure  CheckFailure
	Done     bool
}

type IdleCheck struct{}

type CheckTop struct {
	Package     Package
	Declaration Declaration
	AfterType   bool
}

type CheckNamedType struct {
	Walk TypeWalk
}

func noCheckFailure() CheckFailure {
	return CheckFailure{Diagnostic: validDiagnostic(), Extra: "", Cycle: lean.Array[string]{}}
}

func emptyPackage(source Package) CheckedPackage {
	return CheckedPackage{Source: source, Imports: lean.Array[string]{}, LeanImports: source.LeanImports,
		Declarations: lean.Array[CheckedDeclaration]{}, Laws: lean.Array[CheckedLaw]{}, Folds: 0}
}

func failedCheck(code DiagnosticCode, pos string, detail string) CheckFailure {
	return CheckFailure{Diagnostic: Diagnostic{Code: code, Pos: pos, Detail: detail}, Extra: "", Cycle: lean.Array[string]{}}
}

func (r checkRun) fail(issue Diagnostic) checkRun {
	return r.withFailure(CheckFailure{Diagnostic: issue, Extra: "", Cycle: lean.Array[string]{}})
}

func (r checkRun) withFailure(failure CheckFailure) checkRun {
	return checkRun{Data: r.Data, Stack: r.Stack, Returned: r.Returned, Failure: failure, Done: true}
}

func (r checkRun) withData(data checkData) checkRun {
	return checkRun{Data: data, Stack: r.Stack, Returned: r.Returned, Failure: r.Failure, Done: r.Done}
}

func (r checkRun) withReturn(result checkedReturn) checkRun {
	return checkRun{Data: r.Data, Stack: r.Stack, Returned: result, Failure: r.Failure, Done: r.Done}
}

func (r checkRun) push(task CheckTask) checkRun {
	stack := lean.NewBox(checkStack{Task: task, Rest: r.Stack})
	return checkRun{Data: r.Data, Stack: stack, Returned: r.Returned, Failure: r.Failure, Done: r.Done}
}

func (d checkData) withPackages(packages checkPackages) checkData {
	return checkData{Source: d.Source, Packages: packages, Calls: d.Calls, Seen: d.Seen, Named: d.Named}
}

func (d checkData) withCalls(calls CallGraph) checkData {
	return checkData{Source: d.Source, Packages: d.Packages, Calls: calls, Seen: d.Seen, Named: d.Named}
}

func (d checkData) withNamed(seen lean.OrderedSet[ObjectID], named lean.OrderedMap[ObjectID, CheckedTypeDeclaration]) checkData {
	return checkData{Source: d.Source, Packages: d.Packages, Calls: d.Calls, Seen: seen, Named: named}
}

type stringInsertion struct {
	Values   lean.Array[string]
	Result   lean.Array[string]
	Item     string
	Inserted bool
}

func insertStringStep(index uint, state stringInsertion) stringInsertion {
	entry := state.Values.Get(index).UnwrapOr("")
	if !state.Inserted {
		if state.Item == entry {
			return stringInsertion{Values: state.Values, Result: state.Result.Push(entry), Item: state.Item, Inserted: true}
		}
		if state.Item < entry {
			return stringInsertion{Values: state.Values, Result: state.Result.Push(state.Item).Push(entry), Item: state.Item, Inserted: true}
		}
	}
	return stringInsertion{Values: state.Values, Result: state.Result.Push(entry), Item: state.Item, Inserted: state.Inserted}
}

func insertCheckedString(values lean.Array[string], item string) lean.Array[string] {
	initial := stringInsertion{Values: values, Result: lean.Array[string]{}, Item: item, Inserted: false}
	result := lean.FoldN(values.Size(), initial, insertStringStep)
	if result.Inserted {
		return result.Result
	}
	return result.Result.Push(item)
}

type stringOrder struct {
	Source lean.Array[string]
	Sorted lean.Array[string]
}

func sortCheckedString(index uint, s stringOrder) stringOrder {
	return stringOrder{Source: s.Source, Sorted: insertCheckedString(s.Sorted, s.Source.Get(index).UnwrapOr(""))}
}

func sortedCheckedStrings(items lean.Array[string]) lean.Array[string] {
	return lean.FoldN(items.Size(), stringOrder{Source: items, Sorted: lean.Array[string]{}}, sortCheckedString).Sorted
}

type packageDirectiveLaws struct {
	Source lean.Array[Proposition]
	Laws   lean.Array[CheckedLaw]
}

func appendPackageDirectiveLaw(index uint, s packageDirectiveLaws) packageDirectiveLaws {
	item := s.Source.Get(index).UnwrapOr(Proposition{Name: "", Lean: ""})
	law := CheckedLaw{Proposition: item, Caller: 0, Contracts: lean.Array[ObjectID]{}}
	return packageDirectiveLaws{Source: s.Source, Laws: s.Laws.Push(law)}
}

func (d checkData) discover(path string) checkData {
	if d.Packages.Values.Contains(path) {
		return d
	}
	source := d.Source.PackageOrMissing(path)
	initial := packageDirectiveLaws{Source: source.Laws, Laws: lean.Array[CheckedLaw]{}}
	laws := lean.FoldN(source.Laws.Size(), initial, appendPackageDirectiveLaw).Laws
	pkg := CheckedPackage{Source: source, Imports: lean.Array[string]{}, LeanImports: sortedCheckedStrings(source.LeanImports),
		Declarations: lean.Array[CheckedDeclaration]{}, Laws: laws, Folds: 0}
	next := checkPackages{Values: d.Packages.Values.Insert(path, pkg), Paths: insertCheckedString(d.Packages.Paths, path),
		Schedule: d.Packages.Schedule.Enqueue(source)}
	return d.withPackages(next)
}

func (d checkData) packageState(path string) CheckedPackage {
	return d.Packages.Values.Find(path).UnwrapOr(emptyPackage(d.Source.PackageOrMissing(path)))
}

func (d checkData) updatePackage(path string, pkg CheckedPackage) checkData {
	packages := checkPackages{Values: d.Packages.Values.Insert(path, pkg), Paths: d.Packages.Paths, Schedule: d.Packages.Schedule}
	return d.withPackages(packages)
}

func (d checkData) addDeclaration(path string, decl CheckedDeclaration) checkData {
	next := d.discover(path)
	pkg := next.packageState(path)
	updated := CheckedPackage{Source: pkg.Source, Imports: pkg.Imports, LeanImports: pkg.LeanImports,
		Declarations: pkg.Declarations.Push(decl), Laws: pkg.Laws, Folds: pkg.Folds}
	return next.updatePackage(path, updated)
}

func (d checkData) dependency(path string, target string) checkData {
	next := d.discover(path)
	pkg := next.packageState(path)
	updated := CheckedPackage{Source: pkg.Source, Imports: insertCheckedString(pkg.Imports, target), LeanImports: pkg.LeanImports,
		Declarations: pkg.Declarations, Laws: pkg.Laws, Folds: pkg.Folds}
	return next.updatePackage(path, updated)
}

func (d checkData) addFold(path string, kind FoldFlavor) checkData {
	if kind == 0 {
		return d
	}
	next := d.discover(path)
	pkg := next.packageState(path)
	folded := addFoldFlavor(pkg.Folds, kind)
	updated := CheckedPackage{Source: pkg.Source, Imports: pkg.Imports, LeanImports: pkg.LeanImports,
		Declarations: pkg.Declarations, Laws: pkg.Laws, Folds: folded}
	return next.updatePackage(path, updated)
}

func addFoldFlavor(present FoldFlavor, add FoldFlavor) FoldFlavor {
	// The low four bits represent the four supported fold flavors. Comparing
	// the remainder by ranges avoids Go bitwise operators in modeled code.
	if add == CheckedFoldListUntil {
		if present < CheckedFoldListUntil {
			return present + add
		}
		return present
	}
	if present >= CheckedFoldListUntil {
		return CheckedFoldListUntil + addLowFoldFlavor(present-CheckedFoldListUntil, add)
	}
	return addLowFoldFlavor(present, add)
}

func addLowFoldFlavor(present FoldFlavor, add FoldFlavor) FoldFlavor {
	if add == CheckedFoldList {
		if present < CheckedFoldList {
			return present + add
		}
		return present
	}
	if present >= CheckedFoldList {
		return CheckedFoldList + addTinyFoldFlavor(present-CheckedFoldList, add)
	}
	return addTinyFoldFlavor(present, add)
}

func addTinyFoldFlavor(present FoldFlavor, add FoldFlavor) FoldFlavor {
	if add == CheckedFoldNUntil {
		if present < CheckedFoldNUntil {
			return present + add
		}
		return present
	}
	if present == 0 || present == CheckedFoldNUntil {
		return present + add
	}
	return present
}

func emptyBindingScope() BindingScope {
	return BindingScope{Locals: lean.OrderedMap[ObjectID, int]{}, Next: 0}
}

func emptyBodyState() BodyState {
	return BodyState{Nodes: lean.Array[CheckedExpr]{}, Frames: lean.Box[BodyFrameStack]{},
		Tails: lean.Array[BodyTail]{}, Matches: lean.Array[BodyMatch]{}, Value: 0}
}

func emptyExpressionWalk(source Program) ExprWalk {
	return ExprWalk{Program: source, Scope: emptyBindingScope(), Value: 0,
		Nodes: lean.Array[CheckedExpr]{}, Shape: noCheckedType(), stack: lean.Box[exprFrames]{}}
}

func initialReturn(source Program) checkedReturn {
	return checkedReturn{Type: noCheckedType(), Expr: emptyExpressionWalk(source), Body: emptyBodyState(), Local: emptyCheckLocal(source)}
}

func discoverRoot(index uint, data checkData) checkData {
	return data.discover(data.Source.SelectedPackages.Get(index).UnwrapOr(""))
}

func beginProgramCheck(source Program) checkRun {
	schedule := PackageSchedule{Pending: lean.Array[string]{}, PackageIndex: 0, DeclarationIndex: 0}
	packages := checkPackages{Values: lean.OrderedMap[string, CheckedPackage]{}, Paths: lean.Array[string]{}, Schedule: schedule}
	data := checkData{Source: source, Packages: packages, Calls: CallGraph{States: lean.OrderedMap[ObjectID, FunctionState]{}},
		Seen: lean.OrderedSet[ObjectID]{}, Named: lean.OrderedMap[ObjectID, CheckedTypeDeclaration]{}}
	roots := lean.FoldN(source.SelectedPackages.Size(), data, discoverRoot)
	return checkRun{Data: roots, Stack: lean.Box[checkStack]{}, Returned: initialReturn(source), Failure: noCheckFailure(), Done: false}
}

func (r checkRun) scheduleType(pkg Package, id TypeID, pos string) checkRun {
	walk := StartType(r.Data.Source, r.Data.Seen, pkg, pos, id)
	return r.push(NewCheckTaskCheckNamedType(CheckNamedType{Walk: walk}))
}

type applyTypeEvents struct {
	Data   checkData
	Events lean.Array[TypeEvent]
}

func applyTypeEvent(index uint, s applyTypeEvents) applyTypeEvents {
	fallback := TypeEvent{Package: "", Dependency: "", Declaration: lean.None[CheckedTypeDeclaration]()}
	event := s.Events.Get(index).UnwrapOr(fallback)
	if event.Dependency != "" {
		return applyTypeEvents{Data: s.Data.dependency(event.Package, event.Dependency), Events: s.Events}
	}
	if event.Declaration.IsSome() {
		missing := CheckedTypeDeclaration{Kind: UnsupportedShape, Object: 0, Fields: lean.List[CheckedField]{}, Default: 0, SelfBox: false}
		named := event.Declaration.UnwrapOr(missing)
		decl := CheckedDeclaration{Kind: CheckedNamedType, Object: named.Object, Type: noCheckedType(), Group: lean.Array[ObjectID]{},
			Function: lean.None[CheckedFunction](), Contract: lean.None[CheckedContractDeclaration]()}
		added := s.Data.addDeclaration(event.Package, decl)
		data := added.withNamed(added.Seen, added.Named.Insert(named.Object, named))
		return applyTypeEvents{Data: data, Events: s.Events}
	}
	return s
}

func (r checkRun) checkNamedType(task CheckNamedType) checkRun {
	walk := task.Walk
	if walk.Pending() {
		return r.push(NewCheckTaskCheckNamedType(CheckNamedType{Walk: AdvanceType(walk)}))
	}
	if walk.Exhausted {
		return r.withFailure(failedCheck(TypeCheckBound, walk.Diagnostic.Pos, ""))
	}
	if walk.Cycle.Size() != 0 {
		issue := Diagnostic{Code: EnumZeroCycle, Pos: walk.Diagnostic.Pos, Detail: ""}
		return r.withFailure(CheckFailure{Diagnostic: issue, Extra: "", Cycle: walk.Cycle})
	}
	if walk.Diagnostic.Code != Valid {
		return r.fail(walk.Diagnostic)
	}
	start := applyTypeEvents{Data: r.Data.withNamed(walk.Seen, r.Data.Named), Events: walk.Events}
	applied := lean.FoldN(walk.Events.Size(), start, applyTypeEvent)
	result := checkedReturn{Type: walk.Value, Expr: r.Returned.Expr, Body: r.Returned.Body, Local: r.Returned.Local}
	return r.withData(applied.Data).withReturn(result)
}

func (r checkRun) scan() checkRun {
	step := r.Data.Packages.Schedule.NextDeclaration(r.Data.Source)
	if step.Done {
		return checkRun{Data: r.Data, Stack: r.Stack, Returned: r.Returned, Failure: r.Failure, Done: true}
	}
	packages := checkPackages{Values: r.Data.Packages.Values, Paths: r.Data.Packages.Paths, Schedule: step.Schedule}
	next := r.withData(r.Data.withPackages(packages))
	if step.Declaration.IsSome() {
		decl := step.Declaration.UnwrapOr(Declaration{Pos: "", Object: 0})
		task := CheckTop{Package: step.Package, Declaration: decl, AfterType: false}
		return next.push(NewCheckTaskCheckTop(task))
	}
	return next
}

func (r checkRun) top(task CheckTop) checkRun {
	source := r.Data.Source
	decl := task.Declaration
	obj := source.ObjectOrMissing(decl.Object)
	if task.AfterType {
		return r.finishTop(task, obj)
	}
	issue := source.CheckDeclaration(decl, obj)
	if issue.Code != Valid {
		return r.fail(issue)
	}
	if obj.Kind == FunctionObject {
		return r.push(NewCheckTaskCheckFunctionStart(CheckFunctionStart{Object: decl.Object}))
	}
	next := CheckTop{Package: task.Package, Declaration: decl, AfterType: true}
	resumed := r.push(NewCheckTaskCheckTop(next))
	if obj.Kind == ConstantObject {
		return resumed.scheduleType(task.Package, obj.DefaultType, decl.Pos)
	}
	return resumed.scheduleType(task.Package, obj.Type, decl.Pos)
}

func (r checkRun) finishTop(task CheckTop, obj Object) checkRun {
	source := r.Data.Source
	if obj.Kind == ConstantObject && !source.FitsConstant(obj, task.Package.WordBits) {
		issue := Diagnostic{Code: ConstantOutOfRange, Pos: task.Declaration.Pos, Detail: obj.Name}
		extra := source.TypeOrMissing(obj.DefaultType).Display
		return r.withFailure(CheckFailure{Diagnostic: issue, Extra: extra, Cycle: lean.Array[string]{}})
	}
	if obj.Name == "_" {
		return r
	}
	t := r.Returned.Type
	if obj.Kind == ConstantObject {
		decl := CheckedDeclaration{Kind: CheckedNamedConstant, Object: task.Declaration.Object, Type: t, Group: lean.Array[ObjectID]{},
			Function: lean.None[CheckedFunction](), Contract: lean.None[CheckedContractDeclaration]()}
		return r.withData(r.Data.addDeclaration(task.Package.Path, decl))
	}
	typ := source.TypeOrMissing(obj.Type)
	if (t.Kind == RecordShape || t.Kind == EnumShape) && typ.Kind != AliasType {
		return r
	}
	decl := CheckedDeclaration{Kind: CheckedAlias, Object: task.Declaration.Object, Type: t, Group: lean.Array[ObjectID]{},
		Function: lean.None[CheckedFunction](), Contract: lean.None[CheckedContractDeclaration]()}
	return r.withData(r.Data.addDeclaration(task.Package.Path, decl))
}

func (r checkRun) advance() checkRun {
	if r.Done {
		return r
	}
	if !r.Stack.IsSome() {
		return r.scan()
	}
	top := r.Stack.Get()
	rest := checkRun{Data: r.Data, Stack: top.Rest, Returned: r.Returned, Failure: r.Failure, Done: false}
	switch task := top.Task.Case().(type) {
	case IdleCheck:
		return rest
	case CheckTop:
		return rest.top(task)
	case CheckNamedType:
		return rest.checkNamedType(task)
	case CheckFunctionStart:
		return rest.startFunction(task.Object)
	case CheckFunctionWork:
		return rest.resumeFunction(task)
	case CheckExpressionWork:
		return rest.resumeExpression(task)
	case CheckBodyWork:
		return rest.resumeBody(task)
	}
	return rest
}

type finalizeCheckedPackages struct {
	Data     checkData
	Packages lean.Array[CheckedPackage]
	Failure  CheckFailure
}

func finishCheckedPackage(index uint, state finalizeCheckedPackages) lean.FoldControl[finalizeCheckedPackages] {
	path := state.Data.Packages.Paths.Get(index).UnwrapOr("")
	pkg := state.Data.packageState(path)
	if pkg.Source.Issue != "" {
		return rejectFinalPackage(state, failedCheck(PackageCheckIssue, "", pkg.Source.Issue))
	}
	groups := GroupPackageTypes(pkg.Declarations, state.Data.Named)
	if !groups.Complete {
		return rejectFinalPackage(state, failedCheck(PackageGraphBound, path, ""))
	}
	if groups.Problem != ValidRecursiveTypes {
		return rejectFinalPackage(state, groupFailure(state.Data.Source, path, groups))
	}
	checked := CheckedPackage{Source: pkg.Source, Imports: pkg.Imports, LeanImports: pkg.LeanImports,
		Declarations: groups.Declarations, Laws: pkg.Laws, Folds: pkg.Folds}
	next := finalizeCheckedPackages{Data: state.Data, Packages: state.Packages.Push(checked), Failure: state.Failure}
	return lean.FoldControl[finalizeCheckedPackages]{State: next, Stop: false}
}

func rejectFinalPackage(state finalizeCheckedPackages, failure CheckFailure) lean.FoldControl[finalizeCheckedPackages] {
	result := finalizeCheckedPackages{Data: state.Data, Packages: state.Packages, Failure: failure}
	return lean.FoldControl[finalizeCheckedPackages]{State: result, Stop: true}
}

func groupFailure(source Program, path string, group PackageGroups) CheckFailure {
	from := source.ObjectOrMissing(group.From).Name
	if group.Problem == UnsupportedRecursiveEdge {
		to := source.ObjectOrMissing(group.To).Name
		issue := Diagnostic{Code: RecursiveEdgeIssue, Pos: path, Detail: from}
		return CheckFailure{Diagnostic: issue, Extra: to, Cycle: lean.Array[string]{}}
	}
	return failedCheck(RecursiveRecordIssue, path, from)
}

func stepProgramCheck(_ uint, r checkRun) lean.FoldControl[checkRun] {
	next := r.advance()
	return lean.FoldControl[checkRun]{State: next, Stop: next.Done}
}

func grantTypeChecks(_ uint, r checkRun) lean.FoldControl[checkRun] {
	return lean.FoldNUntil(r.Data.Source.Types.Size()+1, r, stepProgramCheck)
}

func grantObjectChecks(_ uint, r checkRun) lean.FoldControl[checkRun] {
	return lean.FoldNUntil(r.Data.Source.Objects.Size()+1, r, grantTypeChecks)
}

func grantExpressionChecks(_ uint, r checkRun) lean.FoldControl[checkRun] {
	return lean.FoldNUntil(r.Data.Source.Expressions.Size()+1, r, grantObjectChecks)
}

func grantStatementChecks(_ uint, r checkRun) lean.FoldControl[checkRun] {
	return lean.FoldNUntil(r.Data.Source.Statements.Size()+1, r, grantExpressionChecks)
}

func grantPackageChecks(_ uint, r checkRun) lean.FoldControl[checkRun] {
	return lean.FoldNUntil(r.Data.Source.SelectedPackages.Size()+1, r, grantStatementChecks)
}

func failedProgram(source Program, failure CheckFailure, complete bool) CheckResult {
	empty := CheckedProgram{Source: source, Packages: lean.Array[CheckedPackage]{}, NamedTypes: lean.OrderedMap[ObjectID, CheckedTypeDeclaration]{}}
	return CheckResult{Program: empty, Failure: failure, Complete: complete}
}

// Check validates the loaded Go program and produces the complete checked
// representation needed by IR construction. Nested budgets account for
// source occurrences and per-occurrence type traversal without multiplying
// machine-word counts. Exhaustion is an internal failure, not a source error.
//
//golean:export
func (p Program) Check() CheckResult {
	checked := lean.FoldNUntil(32, beginProgramCheck(p), grantPackageChecks)
	run := checked.State
	if !run.Done {
		return failedProgram(p, run.Failure, false)
	}
	if run.Failure.Diagnostic.Code != Valid {
		return failedProgram(p, run.Failure, true)
	}
	initial := finalizeCheckedPackages{Data: run.Data, Packages: lean.Array[CheckedPackage]{}, Failure: noCheckFailure()}
	final := lean.FoldNUntil(run.Data.Packages.Paths.Size(), initial, finishCheckedPackage)
	if final.Stop {
		return failedProgram(p, final.State.Failure, true)
	}
	program := CheckedProgram{Source: p, Packages: final.State.Packages, NamedTypes: run.Data.Named}
	return CheckResult{Program: program, Failure: noCheckFailure(), Complete: true}
}
