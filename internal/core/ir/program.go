package ir

import (
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

// Program is the IR emitted after subset checking.
type Program struct {
	Packages lean.Array[Package]
	Complete bool
}

type namedIR struct {
	Source       loaded.CheckedProgram
	Declarations lean.OrderedMap[string, lean.OrderedMap[string, Declaration]]
}

func modeledSymbol(source loaded.Program, id loaded.ObjectID) Symbol {
	object := source.ObjectOrMissing(id)
	return Symbol{Package: object.Package, Name: object.ModelName}
}

func indexNamedIR(index uint, state namedIR) namedIR {
	id := loaded.ObjectID(index)
	checked := state.Source.NamedTypes.Find(id)
	if !checked.IsSome() {
		return state
	}
	t := checked.UnwrapOr(emptyTypeDeclaration())
	value := DeclarationFromCheckedType(state.Source.Source, t)
	object := modeledSymbol(state.Source.Source, id)
	pkg := state.Declarations.Find(object.Package).UnwrapOr(lean.OrderedMap[string, Declaration]{})
	return namedIR{Source: state.Source, Declarations: state.Declarations.Insert(object.Package, pkg.Insert(object.Name, value))}
}

func emptyTypeDeclaration() loaded.CheckedTypeDeclaration {
	return loaded.CheckedTypeDeclaration{Kind: loaded.UnsupportedShape, Object: 0, Fields: lean.List[loaded.CheckedField]{}, Default: 0, SelfBox: false}
}

func (state namedIR) find(id Symbol) Declaration {
	pkg := state.Declarations.Find(id.Package).UnwrapOr(lean.OrderedMap[string, Declaration]{})
	return pkg.Find(id.Name).UnwrapOr(Declaration{})
}

type zeroResult struct {
	Value    Expr
	Complete bool
}

type zeroDriver struct {
	Context namedIR
	Work    ZeroWalk
}

func advanceZeroDriver(_ uint, driver zeroDriver) lean.FoldControl[zeroDriver] {
	if !driver.Work.Pending() {
		return lean.FoldControl[zeroDriver]{State: driver, Stop: true}
	}
	step := AdvanceZero(driver.Work)
	if step.NeedsDeclaration {
		walk := step.Walk.WithNamedZero(step.Symbol, driver.Context.find(step.Symbol))
		next := zeroDriver{Context: driver.Context, Work: walk}
		return lean.FoldControl[zeroDriver]{State: next, Stop: !walk.Pending()}
	}
	next := zeroDriver{Context: driver.Context, Work: step.Walk}
	return lean.FoldControl[zeroDriver]{State: next, Stop: !step.Walk.Pending()}
}

func zeroTypeBudget(_ uint, driver zeroDriver) lean.FoldControl[zeroDriver] {
	return lean.FoldNUntil(driver.Context.Source.Source.Types.Size()+1, driver, advanceZeroDriver)
}

func zeroFieldBudget(_ uint, driver zeroDriver) lean.FoldControl[zeroDriver] {
	return lean.FoldNUntil(driver.Context.Source.Source.Objects.Size()+1, driver, zeroTypeBudget)
}

func zeroNamedBudget(_ uint, driver zeroDriver) lean.FoldControl[zeroDriver] {
	return lean.FoldNUntil(driver.Context.Source.Source.Objects.Size()+1, driver, zeroFieldBudget)
}

func zeroFromContext(context namedIR, t Type) zeroResult {
	initial := zeroDriver{Context: context, Work: StartZero(t)}
	final := lean.FoldNUntil(6, initial, zeroNamedBudget)
	return zeroResult{Value: final.State.Work.Value, Complete: !final.State.Work.Pending()}
}

type bodyEmit struct {
	Context  namedIR
	Body     lean.Array[loaded.CheckedExpr]
	Nodes    lean.Array[Expr]
	Complete bool
}

func checkedZeroFor(context namedIR, node loaded.CheckedExpr, typ Type) zeroResult {
	if node.Kind == loaded.CheckedZero {
		return zeroFromContext(context, typ)
	}
	if node.Kind == loaded.CheckedPrimitive && loaded.PrimitiveOp(node.Operation) == loaded.OpBoxRead {
		return zeroFromContext(context, checkedBoxElement(context.Source.Source, node.Type))
	}
	return zeroResult{Value: Expr{}, Complete: true}
}

func checkedBoxElement(source loaded.Program, typ loaded.CheckedType) Type {
	if typ.First.IsSome() {
		return TypeFromChecked(source, typ.First.Get())
	}
	return Type{}
}

func emitBodyNode(index uint, state bodyEmit) bodyEmit {
	node := state.Body.Get(index)
	if !node.IsSome() {
		return state
	}
	return appendBodyNode(state, node.UnwrapOr(emptyCheckedExpression()))
}

func emptyExpressionType() loaded.CheckedType {
	return loaded.CheckedType{Kind: loaded.UnsupportedShape, Scalar: loaded.NotScalar, Curated: loaded.UnknownCuratedType,
		Object: 0, First: lean.Box[loaded.CheckedType]{}, Second: lean.Box[loaded.CheckedType]{}}
}

func emptyCheckedExpression() loaded.CheckedExpr {
	return loaded.CheckedExpr{Kind: 0, Type: emptyExpressionType(), Object: 0, Name: "", Operation: 0,
		Abstract: false, Arguments: lean.Array[loaded.CheckedExprID]{}, Binding: 0, Cases: lean.Array[loaded.CheckedMatchCase]{}}
}

func appendBodyNode(state bodyEmit, node loaded.CheckedExpr) bodyEmit {
	source := state.Context.Source.Source
	typ := TypeFromChecked(source, node.Type)
	zero := checkedZeroFor(state.Context, node, typ)
	result := ExpressionFromChecked(node, state.Nodes, typ, modeledSymbol(source, node.Object), zero.Value)
	return bodyEmit{Context: state.Context, Body: state.Body, Nodes: state.Nodes.Push(result),
		Complete: state.Complete && zero.Complete}
}

type parameterBuild struct {
	Source loaded.Program
	Params lean.Array[loaded.CheckedParameter]
	Result lean.List[Binding]
}

func prependParameter(index uint, state parameterBuild) parameterBuild {
	p := state.Params.Get(state.Params.Size() - 1 - index).UnwrapOr(loaded.CheckedParameter{
		Type: emptyExpressionType(), Binding: 0, Name: "", Unused: false})
	value := Binding{ID: p.Binding, Name: p.Name, Type: TypeFromChecked(state.Source, p.Type), Unused: p.Unused}
	return parameterBuild{Source: state.Source, Params: state.Params, Result: lean.Cons(value, state.Result)}
}

type symbolBuild struct {
	Source  loaded.Program
	Objects lean.Array[loaded.ObjectID]
	Result  lean.List[Symbol]
}

func prependSymbol(index uint, state symbolBuild) symbolBuild {
	id := state.Objects.Get(state.Objects.Size() - 1 - index).UnwrapOr(0)
	return symbolBuild{Source: state.Source, Objects: state.Objects, Result: lean.Cons(modeledSymbol(state.Source, id), state.Result)}
}

func symbolsFromChecked(source loaded.Program, ids lean.Array[loaded.ObjectID]) lean.List[Symbol] {
	return lean.FoldN(ids.Size(), symbolBuild{Source: source, Objects: ids, Result: lean.List[Symbol]{}}, prependSymbol).Result
}

type declarationEmit struct {
	Declaration Declaration
	Complete    bool
}

func emitCheckedFunction(context namedIR, symbol Symbol, function loaded.CheckedFunction) declarationEmit {
	source := context.Source.Source
	initial := bodyEmit{Context: context, Body: function.Body, Nodes: lean.Array[Expr]{}, Complete: true}
	body := lean.FoldN(function.Body.Size(), initial, emitBodyNode)
	params := parameterBuild{Source: source, Params: function.Params, Result: lean.List[Binding]{}}
	resolved := lean.FoldN(function.Params.Size(), params, prependParameter)
	value := Function{Symbol: symbol, Params: resolved.Result, Result: TypeFromChecked(source, function.Result),
		Body: checkedOperand(body.Nodes, function.Root), Contracts: symbolsFromChecked(source, function.Contracts), Termination: function.Termination}
	return declarationEmit{Declaration: NewDeclarationFunction(value), Complete: body.Complete}
}

func emptyCheckedFunction() loaded.CheckedFunction {
	return loaded.CheckedFunction{Body: lean.Array[loaded.CheckedExpr]{}, Root: 0, Result: emptyExpressionType(),
		Params: lean.Array[loaded.CheckedParameter]{}, Contracts: lean.Array[loaded.ObjectID]{}, Termination: ""}
}

func emptyCheckedContract() loaded.CheckedContractDeclaration {
	return loaded.CheckedContractDeclaration{Caller: 0, Callee: 0, Assumptions: lean.Array[loaded.Proposition]{},
		Signature: loaded.CheckedContract{Params: lean.List[loaded.ScalarKind]{}, Result: loaded.NotScalar,
			Diagnostic: typeDiagnostic()}}
}

type checkedGroup struct {
	Context  namedIR
	IDs      lean.Array[loaded.ObjectID]
	Declared lean.Array[Declaration]
}

func appendNamedGroup(index uint, state checkedGroup) checkedGroup {
	id := state.IDs.Get(index).UnwrapOr(0)
	named := state.Context.find(modeledSymbol(state.Context.Source.Source, id))
	return checkedGroup{Context: state.Context, IDs: state.IDs, Declared: state.Declared.Push(named)}
}

func emitCheckedDeclaration(context namedIR, value loaded.CheckedDeclaration) declarationEmit {
	source := context.Source.Source
	symbol := modeledSymbol(source, value.Object)
	if value.Kind == loaded.CheckedNamedType {
		return declarationEmit{Declaration: context.find(symbol), Complete: true}
	}
	if value.Kind == loaded.CheckedMutualTypes {
		initial := checkedGroup{Context: context, IDs: value.Group, Declared: lean.Array[Declaration]{}}
		members := lean.FoldN(value.Group.Size(), initial, appendNamedGroup).Declared
		return declarationEmit{Declaration: RecursiveGroupFromDeclarations(members), Complete: true}
	}
	if value.Kind == loaded.CheckedAlias {
		decl := NewDeclarationTypeAlias(TypeAlias{Symbol: symbol, Type: TypeFromChecked(source, value.Type)})
		return declarationEmit{Declaration: decl, Complete: true}
	}
	if value.Kind == loaded.CheckedNamedConstant {
		object := source.ObjectOrMissing(value.Object)
		c := Constant{Type: TypeFromChecked(source, value.Type), Value: object.Value.Value}
		return declarationEmit{Declaration: NewDeclarationNamedConstant(NamedConstant{Symbol: symbol, Value: c}), Complete: true}
	}
	if value.Kind == loaded.CheckedFunctionDecl {
		return emitCheckedFunction(context, symbol, value.Function.UnwrapOr(emptyCheckedFunction()))
	}
	contract := value.Contract.UnwrapOr(emptyCheckedContract())
	item := ContractFromChecked(modeledSymbol(source, contract.Caller), modeledSymbol(source, contract.Callee), contract.Assumptions, contract.Signature)
	return declarationEmit{Declaration: NewDeclarationContract(item), Complete: true}
}

type declarationList struct {
	Context      namedIR
	Source       lean.Array[loaded.CheckedDeclaration]
	Declarations lean.List[Declaration]
	Complete     bool
}

func prependCheckedDeclaration(index uint, state declarationList) declarationList {
	checked := state.Source.Get(state.Source.Size() - 1 - index)
	if !checked.IsSome() {
		return state
	}
	item := checked.UnwrapOr(loaded.CheckedDeclaration{Kind: 0, Object: 0, Type: emptyExpressionType(), Group: lean.Array[loaded.ObjectID]{},
		Function: lean.None[loaded.CheckedFunction](), Contract: lean.None[loaded.CheckedContractDeclaration]()})
	value := emitCheckedDeclaration(state.Context, item)
	return declarationList{Context: state.Context, Source: state.Source, Declarations: lean.Cons(value.Declaration, state.Declarations),
		Complete: state.Complete && value.Complete}
}

type lawBuild struct {
	Source loaded.Program
	Laws   lean.Array[loaded.CheckedLaw]
	Result lean.List[Law]
}

func prependCheckedLaw(index uint, state lawBuild) lawBuild {
	fallback := loaded.CheckedLaw{Proposition: loaded.Proposition{Name: "", Lean: ""}, Caller: 0, Contracts: lean.Array[loaded.ObjectID]{}}
	law := state.Laws.Get(state.Laws.Size() - 1 - index).UnwrapOr(fallback)
	prop := Proposition{Name: law.Proposition.Name, Lean: law.Proposition.Lean}
	value := Law{Proposition: prop, Caller: modeledSymbol(state.Source, law.Caller), Contracts: symbolsFromChecked(state.Source, law.Contracts)}
	return lawBuild{Source: state.Source, Laws: state.Laws, Result: lean.Cons(value, state.Result)}
}

type stringBuild struct {
	Source lean.Array[string]
	Result lean.List[string]
}

func prependString(index uint, state stringBuild) stringBuild {
	value := state.Source.Get(state.Source.Size() - 1 - index).UnwrapOr("")
	return stringBuild{Source: state.Source, Result: lean.Cons(value, state.Result)}
}

func stringsFromChecked(values lean.Array[string]) lean.List[string] {
	return lean.FoldN(values.Size(), stringBuild{Source: values, Result: lean.List[string]{}}, prependString).Result
}

type programBuild struct {
	Context namedIR
	Result  Program
}

func emitPackage(index uint, state programBuild) programBuild {
	item := state.Context.Source.Packages.Get(index)
	if !item.IsSome() {
		return state
	}
	pkg := item.UnwrapOr(loaded.CheckedPackage{Source: state.Context.Source.Source.PackageOrMissing(""),
		Imports: lean.Array[string]{}, LeanImports: lean.Array[string]{}, Declarations: lean.Array[loaded.CheckedDeclaration]{},
		Laws: lean.Array[loaded.CheckedLaw]{}, Folds: 0})
	initial := declarationList{Context: state.Context, Source: pkg.Declarations, Declarations: lean.List[Declaration]{}, Complete: true}
	decls := lean.FoldN(pkg.Declarations.Size(), initial, prependCheckedDeclaration)
	laws := lawBuild{Source: state.Context.Source.Source, Laws: pkg.Laws, Result: lean.List[Law]{}}
	value := Package{Path: pkg.Source.Path, Name: pkg.Source.Name, Dir: pkg.Source.Dir, Word: wordFromLoaded(pkg.Source.WordBits),
		Imports: stringsFromChecked(pkg.Imports), LeanImports: stringsFromChecked(pkg.LeanImports),
		Decls: decls.Declarations, Laws: lean.FoldN(pkg.Laws.Size(), laws, prependCheckedLaw).Result, Folds: FoldKind(pkg.Folds)}
	result := Program{Packages: state.Result.Packages.Push(value), Complete: state.Result.Complete && decls.Complete}
	return programBuild{Context: state.Context, Result: result}
}

func wordFromLoaded(bits int) Kind {
	if bits == 32 {
		return UInt32
	}
	return UInt64
}

// FromLoaded constructs IR from a validated program. Its only failure status
// indicates an internal traversal bound was exhausted.
//
//golean:export
func FromLoaded(program loaded.CheckedProgram) Program {
	initial := namedIR{Source: program, Declarations: lean.OrderedMap[string, lean.OrderedMap[string, Declaration]]{}}
	named := lean.FoldN(program.Source.Objects.Size(), initial, indexNamedIR)
	state := programBuild{Context: named, Result: Program{Packages: lean.Array[Package]{}, Complete: true}}
	return lean.FoldN(program.Packages.Size(), state, emitPackage).Result
}
