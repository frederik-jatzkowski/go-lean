// Package lower converts checked SSA into structured Lean-ready IR.
package lower

import (
	"maps"
	"net/url"
	"slices"
	"strconv"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

func FromSSA(input Input, sourceStem string, wordBits int64) ir.Program {
	return FromSSAWithAbstractCalls(input, sourceStem, wordBits, nil)
}

// FromSSAWithAbstractCalls lowers designated direct calls as total operations.
func FromSSAWithAbstractCalls(input Input, sourceStem string, wordBits int64, abstract map[ir.Symbol]map[ir.Symbol]bool) ir.Program {
	program := ir.Program{Records: make(map[ir.Type]ir.Record), Contracts: make(map[ir.Type]ir.Contract)}
	file := url.PathEscape(sourceStem)
	reader := inputReader{input: input, objects: make(map[int64]any)}
	// The checker orders callees before callers, so their effects are already known.
	facts := &functionFacts{store: stateSnapshot{}}
	instances := make(map[*sourceFunction]string)
	var functions []*sourceFunction
	for i := int64(0); i < input.FunctionCount(); i++ {
		functions = append(functions, reader.decodeFunction(input.FunctionAt(i)))
	}
	nullableSlices := usesNullableSlices(functions)
	capacitySlices := capacitySliceTypes(functions)
	for _, fn := range functions {
		if fn.Origin != "" {
			instances[fn] = fn.Origin + "$instance" + strconv.Itoa(len(instances))
		}
		l := lowerer{
			root: input.PackagePath(), input: input, file: file, state: stateSnapshot{}, binders: new([]ir.Binder), facts: facts,
			records: program.Records, instances: instances,
			contracts: program.Contracts, usedContracts: make(map[ir.Type]bool),
			nullableSlices: nullableSlices && fn.Stateful == nil, capacitySlices: capacitySlices,
		}
		if method := fn.Stateful; method != nil {
			program.Functions = append(program.Functions, l.lowerStateful(fn, method)...)
			if l.usesWord {
				program.WordBits = wordBits
			}
			continue
		}
		result := ir.Function{Symbol: l.symbol(fn), Result: productType(fn.Results, l.ordinaryType)}
		l.abstract = abstract[result.Symbol]
		for i := 0; i < fn.TypeParameters; i++ {
			result.TypeParams = append(result.TypeParams, ir.TypeParameter(i))
		}
		for _, capture := range fn.FreeVars {
			result.Params = append(result.Params, l.bindAs(capture, l.captureType(capture)))
		}
		chain := fn.Chain
		for _, param := range fn.Params {
			if build := fn.Build; build != nil && param == build.Callback {
				result.Params = append(result.Params, l.bindAs(param, build.CallbackType))
			} else if chain != nil && param == chain.Input {
				result.Params = append(result.Params, l.bindAs(param, ir.SliceType(chain.Element)))
			} else {
				result.Params = append(result.Params, l.bind(param))
			}
		}
		if loop := fn.Counted; loop != nil {
			if loop.Structured != nil {
				l.lowerStructuredCountedLoop(&result, loop)
			} else {
				l.lowerCountedLoop(&result, loop)
			}
		} else if fold := fn.Range; fold != nil {
			if fold.Excluded != nil {
				result.Body.Result = ir.Return{Value: ir.CollectionFold{Sequence: l.sliceList(fold.Source), Excluded: l.value(fold.Excluded)}}
			} else if fold.Structured != nil {
				result.Body.Result = l.lowerStructuredFold(fold)
			} else {
				result.Body.Result = l.lowerRangeFold(fold)
			}
		} else if build := fn.Build; build != nil {
			if build.Exit != nil {
				result.Body = l.lowerSliceResults(build)
			} else if build.Element == nil {
				l.canPanic = true
				value := l.sliceList(build.Source)
				value = l.freshSlice(value, fn.Results[0].Model)
				result.Body.Result = ir.Return{Value: value}
			} else {
				traversal := l.lowerSliceBuild(build)
				if l.nullableSlice(fn.Results[0].Model) {
					destination := l.freshBinder("slice", l.valueType(fn.Results[0]))
					traversal.Destination = &destination
					traversal.Continuation = &ir.Body{Result: ir.Return{Value: l.freshSlice(ir.Ref(destination), fn.Results[0].Model)}}
				}
				result.Body.Result = traversal
			}
		} else if chain != nil {
			result.Body.Result = l.lowerChainRecursion(chain)
		} else {
			result.Body = l.body(fn.Entry, nil)
		}
		if l.usesWord {
			program.WordBits = wordBits
		}
		result.Contracts = slices.Sorted(maps.Keys(l.usedContracts))
		result.CanPanic = l.canPanic
		program.Functions = append(program.Functions, result)
		facts.record(fn, result.CanPanic, result.Contracts)
	}
	return program
}

// lookupBindingID resolves a source value in the current branch's store.
//
//golean:verify lookupAfterBinding : ∀ {S : Type} (store : InterfaceContracts.StateStoreContract S) (state : S) (value binder : Int64),
//golean:verify+   lookupBindingID store (store.Bind state value binder) value = (binder, true)
//golean:verify interveningBindingsPreserveLookup : ∀ {S : Type} (store : InterfaceContracts.StateStoreContract S) (state : S) (value : Int64)
//golean:verify+   (writes : List (Int64 × Int64)) (distinct : ∀ entry ∈ writes, value ≠ entry.1),
//golean:verify+   lookupBindingID store (writes.foldl (fun s entry => store.Bind s entry.1 entry.2) state) value =
//golean:verify+   lookupBindingID store state value
func lookupBindingID(state StateStore, value int64) (int64, bool) {
	if !state.HasBinding(value) {
		return 0, false
	}
	return state.LookupBinding(value), true
}

// recordEmission records the effect fact after a definition has been emitted.
//
//golean:export
func recordEmission(state StateStore, function int64, canPanic bool) StateStore {
	if canPanic {
		return state.PutFact(function, effectFact, 1)
	}
	return state.PutFact(function, effectFact, 0)
}

// lookupEmission distinguishes a known pure definition from an absent one.
//
//golean:verify lookupAfterEmission : ∀ {S : Type} (store : InterfaceContracts.StateStoreContract S) (state : S) (function : Int64)
//golean:verify+   (effect : Bool),
//golean:verify+   lookupEmission store (recordEmission store state function effect) function = (effect, true)
//golean:verify writingDependencyIndexPreservesEmission : ∀ {S : Type} (store : InterfaceContracts.StateStoreContract S) (state : S)
//golean:verify+   (function callee dependencyIndex : Int64),
//golean:verify+   lookupEmission store (store.PutFact state function 1 dependencyIndex) callee =
//golean:verify+   lookupEmission store state callee
//golean:verify interveningEmissionsPreserveCallee : ∀ {S : Type} (store : InterfaceContracts.StateStoreContract S) (state : S) (callee : Int64)
//golean:verify+   (effect : Bool) (later : List (Int64 × Bool)) (distinct : ∀ entry ∈ later, callee ≠ entry.1),
//golean:verify+   lookupEmission store
//golean:verify+   (later.foldl (fun s entry => recordEmission store s entry.1 entry.2)
//golean:verify+   (recordEmission store state callee effect)) callee = (effect, true)
func lookupEmission(state StateStore, function int64) (bool, bool) {
	if !state.HasFact(function, effectFact) {
		return false, false
	}
	return state.LookupFact(function, effectFact) != 0, true
}

func (l *lowerer) lowerCountedLoop(fn *ir.Function, loop *sourceCounted) {
	helper := ir.CountedLoop{Symbol: fn.Symbol, State: l.bind(loop.State)}
	helper.Symbol.Name += "$loop"
	call := ir.Call{Callee: helper.Symbol}
	for _, param := range fn.Params {
		if param.Type == ir.Int64 {
			helper.Params = append(helper.Params, param)
			call.Args = append(call.Args, ir.Ref(param))
		}
	}
	helper.Steps = l.lowerPureSteps(loop.Steps)
	fn.Body.Bindings = l.lowerPureSteps(loop.Before)
	helper.Next = l.value(loop.Next)
	call.Args = append(call.Args, ir.LoopFuel{Start: l.value(loop.Start), Bound: l.value(loop.Bound),
		Signed: !loop.Bound.Type.Model.IsUnsigned(), ZeroStart: loop.Start.IsZero}, l.value(loop.Initial))
	if loop.Result == loop.State && len(loop.After) == 0 {
		fn.Body.Result = ir.Return{Value: call}
	} else {
		fn.Body.Bindings = append(fn.Body.Bindings, ir.Binding{Binder: helper.State, Value: call})
		fn.Body.Bindings = append(fn.Body.Bindings, l.lowerPureSteps(loop.After)...)
		fn.Body.Result = ir.Return{Value: l.value(loop.Result)}
	}
	fn.Loop = &helper
}

func (l *lowerer) lowerRangeFold(fold *sourceRange) ir.ListFold {
	result := ir.ListFold{
		Sequence: l.sliceList(fold.Source), Initial: l.value(fold.Initial),
		State: l.bind(fold.State), Element: l.bind(fold.Element),
	}
	result.Steps = l.lowerPureSteps(fold.Steps)
	result.Next = l.value(fold.Next)
	return result
}

func (l *lowerer) lowerSliceResults(build *sourceBuild) ir.Body {
	var body ir.Body
	for _, length := range build.Lengths {
		body.Bindings = append(body.Bindings, ir.Binding{Binder: l.bind(length),
			Value: ir.SliceLength{List: l.sliceList(build.Source)}})
	}
	if build.Copy != nil {
		body.Bindings = append(body.Bindings, ir.Binding{Binder: l.bind(build.Copy),
			Value: ir.SliceLength{List: l.sliceList(build.Source)}})
	}
	destination := l.bind(build.Destination)
	if build.Element == nil {
		l.canPanic = true
		value := l.sliceList(build.Source)
		value = l.freshSlice(value, build.Destination.Type.Model)
		body.Bindings = append(body.Bindings, ir.Binding{Binder: destination, Value: value})
		exit := l.instructions(build.Exit, nil, build.ExitStart)
		body.Bindings = append(body.Bindings, exit.Bindings...)
		body.Result = exit.Result
	} else {
		result := l.lowerSliceBuild(build)
		exit := l.instructions(build.Exit, nil, build.ExitStart)
		result.Destination, result.Continuation = &destination, &exit
		if l.nullableSlice(build.Destination.Type.Model) {
			raw := l.freshBinder("slice", l.valueType(build.Destination.Type))
			result.Destination = &raw
			exit.Bindings = append([]ir.Binding{{Binder: destination, Value: l.freshSlice(ir.Ref(raw), build.Destination.Type.Model)}}, exit.Bindings...)
		}
		body.Result = result
	}
	return body
}

func (l *lowerer) lowerSliceBuild(build *sourceBuild) ir.ListBuild {
	result := ir.ListBuild{Sequence: l.sliceList(build.Source), Element: l.bind(build.Element), Effectful: build.Effectful}
	if iter := build.Iteration; iter != nil {
		l.iteration = &iteration{header: iter.Header, skip: iter.Skip, stores: iter.Stores}
		body := l.body(iter.Entry, iter.Header)
		result.Body, result.Effectful = &body, l.canPanic
		l.iteration = nil
	}
	l.canPanic = true // Keep the checked construction in the panic-result model.
	if result.Body != nil {
		return result
	}
	if build.Effectful {
		result.Next = ir.Apply{Function: l.value(build.Callback), Argument: ir.Ref(result.Element)}
		return result
	}
	result.Steps = l.lowerPureSteps(build.Steps)
	result.Next = l.value(build.Value)
	return result
}

func (l *lowerer) lowerChainRecursion(chain *sourceChain) ir.ListRecursion {
	input := l.mustBinding(chain.Input)
	result := ir.ListRecursion{Input: input, Tail: l.bindAs(chain.Tail, input.Type), Base: packResults(chain.Base, l.value)}
	if chain.Head != nil {
		head := l.bind(chain.Head)
		result.Head = &head
	}
	result.Step.Bindings = l.lowerPureSteps(chain.Steps)
	result.Step.Result = ir.Return{Value: packResults(chain.Result, l.value)}
	return result
}

func (l *lowerer) lowerPureSteps(values []*sourceValue) []ir.Binding {
	var steps []ir.Binding
	for _, step := range values {
		var expr ir.Expr
		switch step.Kind {
		case binaryValue:
			expr = l.binary(step)
		case unaryValue:
			expr = ir.Negate{Value: l.value(step.X)}
		case extractValue:
			expr = l.project(step)
		case callValue:
			arg := l.value(step.Call.Args[0])
			if callee := step.Call.Target; callee != nil {
				call := ir.SelfCall{Name: l.symbol(callee).Name, Args: []ir.Expr{arg}}
				for _, arg := range step.Call.Args[1:] {
					call.Args = append(call.Args, l.value(arg))
				}
				expr = call
			} else {
				expr = ir.Apply{Function: l.value(step.Call.Value), Argument: arg}
			}
		}
		steps = append(steps, ir.Binding{Binder: l.bind(step), Value: expr})
	}
	return steps
}

type iteration struct {
	header     *sourceBlock
	skip       []*sourceValue
	stores     []*sourceStore
	stored     ir.Expr
	backValues []*sourceBackEdge
}

type lowerer struct {
	abstract       map[ir.Symbol]bool
	iteration      *iteration
	root           string
	input          Input
	file           string
	state          StateStore
	binders        *[]ir.Binder
	facts          *functionFacts
	canPanic       bool
	usesWord       bool
	nullableSlices bool
	capacitySlices map[ir.Type]bool
	records        map[ir.Type]ir.Record
	instances      map[*sourceFunction]string
	contracts      map[ir.Type]ir.Contract
	usedContracts  map[ir.Type]bool
}

func (l *lowerer) symbol(fn *sourceFunction) ir.Symbol {
	symbol := ir.Symbol{Package: l.root, File: l.file, Name: fn.Name}
	if fn.Receiver != "" {
		symbol.Name = fn.Receiver + "$" + fn.Name
	}
	if name, ok := l.instances[fn]; ok {
		symbol.Name = name
	}
	if fn.Package != l.root {
		symbol.Dependency = fn.Package
	}
	return symbol
}

func (l *lowerer) bind(value *sourceValue) ir.Binder {
	return l.bindAs(value, l.ordinaryType(value.Type))
}

func (l *lowerer) bindAs(value *sourceValue, typ ir.Type) ir.Binder {
	binder := l.freshBinder(value.Name, typ)
	l.state = l.state.Bind(value.ID, int64(len(*l.binders)))
	*l.binders = append(*l.binders, binder)
	return binder
}

func (l *lowerer) body(block, predecessor *sourceBlock) ir.Body {
	if l.iteration != nil && block == l.iteration.header {
		value := l.iteration.stored
		if l.iteration.backValues != nil {
			value = packResults(backEdgeValues(l.iteration.backValues, predecessor), l.value)
		}
		return ir.Body{Result: ir.Return{Value: value}}
	}
	return l.instructions(block, predecessor, 0)
}

func (l *lowerer) instructions(block, predecessor *sourceBlock, start int) ir.Body {
	var result ir.Body
	for _, ins := range block.Instructions[start:] {
		if l.iteration != nil && slices.Contains(l.iteration.skip, ins) {
			if value := storedValue(l.iteration.stores, ins); value != nil {
				l.iteration.stored = l.value(value)
			}
			continue
		}
		switch ins.Kind {
		case binaryValue:
			if ins.X.Type.Model.SliceElem() != "" {
				slice := ins.X
				if ins.X.IsNil {
					slice = ins.Y
				}
				var value ir.Expr = ir.OptionIsSome{Value: l.value(slice)}
				if ins.Op == ir.Equal {
					value = ir.Not{Value: value}
				}
				result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: value})
				continue
			}
			value := l.binary(ins)
			canPanic := value.Op.PanicsOnZeroDivisor()
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins), Value: value, CanPanic: canPanic,
			})
			l.canPanic = l.canPanic || canPanic
		case unaryValue:
			var value ir.Expr
			canPanic := false
			switch {
			case ins.Not:
				value = ir.Not{Value: l.value(ins.X)}
			case ins.Dereference:
				canPanic = ins.ReadOnly
				if canPanic {
					value = l.value(ins.X)
				} else {
					value = l.load(ins.X)
				}
			default:
				value = ir.Negate{Value: l.value(ins.X)}
			}
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins), Value: value, CanPanic: canPanic,
			})
			l.canPanic = l.canPanic || canPanic
		case fieldValue:
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins),
				Value:  ir.RecordField{Value: l.value(ins.X), Name: ins.Field},
			})
		case fieldAddress:
			if ins.ReadOnly {
				binder := l.bindAs(ins, l.valueType(ins.FieldType))
				source := l.value(ins.X)
				nested := ins.X.Kind == fieldAddress
				var value ir.Expr = ir.RecordField{Value: source, Name: ins.Field}
				if !nested {
					value = ir.CheckedRecordField{Value: source, Type: l.valueType(ins.RecordType), Name: ins.Field}
					l.canPanic = true
				}
				result.Bindings = append(result.Bindings, ir.Binding{
					Binder: binder, Value: value, CanPanic: !nested,
				})
			}
		case indexAddress, indexValue:
			if ins.Kind == indexAddress && ins.X.ArrayInitial == nil && ins.X.Type.Elem != nil {
				if elem, _ := ins.X.Type.Elem.Model.ArrayShape(); elem != "" && ins.IndexInBounds {
					// A local array address has no remaining check in this branch.
					continue
				}
			}
			result.Bindings = append(result.Bindings, l.checkedIndex(ins, ins.X, ins.IndexValue))
		case stringSliceValue:
			value := ir.CheckedStringSlice{Bytes: l.value(ins.X)}
			if ins.Y != nil {
				value.Low, value.LowType = l.value(ins.Y), l.valueType(ins.Y.Type)
			}
			if ins.IndexValue != nil {
				value.High, value.HighType = l.value(ins.IndexValue), l.valueType(ins.IndexValue.Type)
			}
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: value, CanPanic: true})
			l.canPanic = true
		case concreteErrorValue:
			value := ir.Some{Value: ir.StringLiteral(ins.Text)}
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: value})
		case appendValue:
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins),
				Value: ir.SliceAppend{Slice: l.value(ins.X), Element: l.value(ins.Y)}})
		case emptySliceValue:
			value := l.freshSlice(ir.EmptySlice{}, ins.Type.Model)
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: value})
		case makeMap:
			l.canPanic = true // Keep the fresh map result in the panic-result model.
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: ir.EmptyMap{}})
		case mapUpdate:
			// The checker proved exclusive access, so a new binding can replace
			// the map state without losing observations through other aliases.
			update := ir.MapUpdate{Map: l.value(ins.X), Key: l.value(ins.Key), Value: l.value(ins.Value)}
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins.X), Value: update})
		case mapLookup:
			_, elem := l.valueType(ins.X.Type).MapShape()
			typ := ir.OptionType(elem)
			var value ir.Expr = ir.MapLookup{Map: l.value(ins.X), Key: l.value(ins.IndexValue)}
			if !ins.CommaOK {
				typ = elem
				value = ir.OptionGetD{Value: value, Default: ir.IntLiteral{Value: "0", Type: elem}}
			}
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bindAs(ins, typ), Value: value})
		case extractValue:
			binder := l.bind(ins)
			if ins.X.Kind == callValue {
				result.Bindings = append(result.Bindings, ir.Binding{Binder: binder, Value: l.project(ins)})
				continue
			}
			lookup := l.value(ins.X)
			var value ir.Expr = ir.OptionIsSome{Value: lookup}
			if ins.OperandIndex == 0 {
				value = ir.OptionGetD{Value: lookup, Default: ir.IntLiteral{Value: "0", Type: binder.Type}}
			}
			result.Bindings = append(result.Bindings, ir.Binding{Binder: binder, Value: value})
		case callValue:
			if ins.Call.Method != "" {
				receiver := ins.Call.Value
				call := ir.InterfaceCall{
					Contract: l.valueType(receiver.Type), Method: ins.Call.Method,
					Args: []ir.Expr{l.value(receiver)},
				}
				for _, arg := range ins.Call.Args {
					call.Args = append(call.Args, l.value(arg))
				}
				result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: call})
				continue
			}
			if ins.Call.Length {
				arg := ins.Call.Args[0]
				value := l.value(arg)
				var length ir.Expr = ir.ByteLen{Value: value}
				if arg.Type.Model.SliceElem() != "" {
					length = ir.SliceLength{List: l.sliceList(arg)}
				}
				result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: length})
				continue
			}
			if ins.Call.Capacity {
				result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: ir.SliceCapacity{Slice: l.value(ins.Call.Args[0])}})
				continue
			}
			if ins.Call.Extremum != "" {
				value := ir.IntegerExtremum{Max: ins.Call.Extremum == "max"}
				for _, arg := range ins.Call.Args {
					value.Args = append(value.Args, l.value(arg))
				}
				result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: value})
				continue
			}
			target := ins.Call.Target
			call := ir.Call{Callee: l.symbol(target)}
			abstract := l.abstract[call.Callee]
			if !abstract {
				call.Contracts = l.facts.contracts(target)
			}
			for _, contract := range call.Contracts {
				l.usedContracts[contract] = true
			}
			if closure := ins.Call.Value; closure.Kind == closureValue {
				for _, capture := range closure.Values {
					call.Args = append(call.Args, l.value(capture))
				}
			}
			var build *sourceBuild
			if !abstract {
				build = target.Build
			}
			for i, arg := range ins.Call.Args {
				if build != nil && target.Params[i] == build.Callback {
					call.Args = append(call.Args, l.sliceCallback(arg, build.Effectful))
				} else {
					call.Args = append(call.Args, l.value(arg))
				}
			}
			canPanic := !abstract && l.facts.effect(target)
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins), Value: call, CanPanic: canPanic,
			})
			l.canPanic = l.canPanic || canPanic
		case convertValue:
			binder := l.bind(ins)
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: binder, Value: ir.Convert{Value: l.value(ins.X), From: l.valueType(ins.X.Type), To: binder.Type},
			})
		case changeType:
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: l.value(ins.X)})
		case allocValue:
			if ins.MutableCell {
				typ := ins.Type.Elem
				value := l.zeroValue(typ)
				result.Bindings = append(result.Bindings, ir.Binding{
					Binder: l.bindAs(ins, l.valueType(typ)), Value: value,
				})
			}
		case storeValue:
			root := ins.X
			for root.Kind == fieldAddress || root.Kind == indexAddress {
				root = root.X
			}
			if root.HasCell {
				if root.MutableCell {
					value := l.recordStore(ins.X, l.value(ins.Value))
					typ := l.valueType(root.Type.Elem)
					result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bindAs(root, typ), Value: value})
				}
				continue
			}
			if ins.X.ArrayInitial != nil || ins.X.Kind == fieldAddress {
				continue
			}
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bindAs(ins.X, l.captureType(ins.X)), Value: l.value(ins.Value),
			})
		case ifValue:
			condition := l.value(ins.X)
			incoming := l.state
			var stored ir.Expr
			if l.iteration != nil {
				stored = l.iteration.stored
			}
			then := l.body(block.Succs[0], block)
			l.state = restoreBindings(incoming, l.state)
			if l.iteration != nil {
				l.iteration.stored = stored
			}
			otherwise := l.body(block.Succs[1], block)
			result.Result = ir.If{Condition: condition, Then: then, Else: otherwise}
		case phiValue:
			// Each branch contains only the computations along its own path.
			value := l.phiValue(ins, predecessor, l.value)
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: value})
		case returnValue:
			result.Result = ir.Return{Value: packResults(ins.Values, l.value)}
		case jumpValue:
			next := l.body(block.Succs[0], block)
			result.Bindings = append(result.Bindings, next.Bindings...)
			result.Result = next.Result
		}
	}
	return result
}

func (l *lowerer) checkedIndex(value, sequence, index *sourceValue) ir.Binding {
	var input ir.Expr
	sequenceType := sequence.Type
	if init := sequence.ArrayInitial; init != nil {
		sequence = init
		sequenceType = init.Type
	} else if value.Kind == indexAddress && sequence.Type.Elem != nil {
		if elem, _ := sequence.Type.Elem.Model.ArrayShape(); elem != "" {
			sequenceType = sequence.Type.Elem
			input = l.load(sequence)
		}
	}
	if input == nil {
		input = l.value(sequence)
	}
	typ := l.valueType(sequenceType)
	elem := typ.SliceElem()
	if elem == "" {
		elem, _ = typ.ArrayShape()
	} else {
		input = l.sliceElements(input, typ)
	}
	if value.IndexInBounds && value.Kind == indexValue {
		return ir.Binding{Binder: l.bindAs(value, elem), Value: ir.ArrayGet{
			Sequence: input, Index: l.value(index), IndexType: l.valueType(index.Type), Default: l.zeroValue(sequenceType.Elem),
		}}
	}
	l.canPanic = true
	return ir.Binding{
		Binder: l.bindAs(value, elem),
		Value: ir.CheckedIndex{
			Sequence: input, SequenceType: typ, Index: l.value(index), IndexType: l.valueType(index.Type),
		},
		CanPanic: true,
	}
}

func (l *lowerer) value(value *sourceValue) ir.Expr {
	if value.Kind == functionValue {
		return ir.FunctionRef(l.symbol(value.Target))
	}
	if value.Kind == constantValue {
		typ := l.valueType(value.Type)
		if typ.Pointee() != "" {
			return ir.NilPointer{}
		}
		if typ.SliceElem() != "" {
			if l.nullableSlice(typ) {
				return ir.NilPointer{}
			}
			return ir.EmptySlice{}
		}
		if key, _ := typ.MapShape(); key != "" {
			return ir.EmptyMap{}
		}
		if value.IsNil {
			return l.zeroValue(value.Type)
		}
		switch typ {
		case ir.Bool:
			return ir.BoolLiteral(value.Boolean)
		case ir.Bytes:
			return ir.BytesLiteral(value.Text)
		case ir.Float32:
			return ir.Float32Literal(value.Bits)
		case ir.Float64:
			return ir.Float64Literal(value.Bits)
		}
		return ir.IntLiteral{Value: value.Text, Type: typ}
	}
	if binder, ok := l.binding(value); ok {
		return ir.Ref(binder)
	}
	panic("missing binding for checked SSA value: " + value.Name)
}

func (l *lowerer) binary(expr *sourceValue) ir.Binary {
	return ir.Binary{Op: expr.Op, Left: l.value(expr.X), Right: l.value(expr.Y), OperandType: l.valueType(expr.X.Type)}
}

func productType(results []*sourceType, valueType func(*sourceType) ir.Type) ir.Type {
	if len(results) == 0 {
		return ir.Unit
	}
	last := len(results) - 1
	typ := valueType(results[last])
	for i := last - 1; i >= 0; i-- {
		typ = ir.ProductType(valueType(results[i]), typ)
	}
	return typ
}

func packResults(results []*sourceValue, value func(*sourceValue) ir.Expr) ir.Expr {
	if len(results) == 0 {
		return ir.UnitLiteral{}
	}
	last := len(results) - 1
	result := value(results[last])
	for i := last - 1; i >= 0; i-- {
		result = ir.Pair{Left: value(results[i]), Right: result}
	}
	return result
}

func (l *lowerer) project(extract *sourceValue) ir.Expr {
	value := l.value(extract.X)
	for i := 0; i < extract.OperandIndex; i++ {
		value = ir.PairField{Value: value, Second: true}
	}
	if extract.OperandIndex < len(extract.X.Type.Tuple)-1 {
		value = ir.PairField{Value: value}
	}
	return value
}

func (l *lowerer) valueType(t *sourceType) ir.Type {
	if t.IsTuple {
		return productType(t.Tuple, l.valueType)
	}
	typ := t.Model
	if t.IsInterface {
		l.useContract(t, typ)
		return typ
	}
	l.usesWord = l.usesWord || typ.IsWord()
	elem, _ := typ.ArrayShape()
	if typ.Pointee() != "" || typ.SliceElem() != "" || elem != "" {
		l.valueType(t.Elem)
	}
	if key, value := typ.MapShape(); key != "" {
		l.usesWord = l.usesWord || key.IsWord() || value.IsWord()
	}
	if typ.IsRecord() {
		if _, exists := l.records[typ]; !exists {
			record := ir.Record{Symbol: l.typeSymbol(t, "")}
			handles := make(map[ir.Type]bool)
			for _, field := range t.Fields {
				fieldType := l.recordFieldType(l.valueType(field.Type))
				record.Fields = append(record.Fields, ir.Field{Name: field.Name, Type: fieldType})
				if field.Type.IsInterface {
					handles[fieldType] = true
				}
				for _, handle := range l.records[fieldType].Handles {
					handles[handle] = true
				}
			}
			record.Handles = slices.Sorted(maps.Keys(handles))
			l.records[typ] = record
		} else {
			for _, handle := range l.records[typ].Handles {
				l.usedContracts[handle] = true
			}
		}
	}
	return typ
}

func (l *lowerer) ordinaryType(t *sourceType) ir.Type {
	if t.IsTuple {
		return productType(t.Tuple, l.ordinaryType)
	}
	typ := l.valueType(t)
	if l.nullableSlice(typ) {
		return l.recordFieldType(typ)
	}
	return typ
}

func (l *lowerer) hasCapacity(typ ir.Type) bool {
	return typ.SliceElem() == ir.Bytes || l.capacitySlices[typ]
}

func (l *lowerer) recordFieldType(typ ir.Type) ir.Type {
	if l.hasCapacity(typ) {
		return ir.OptionType(ir.ProductType(typ, ir.Nat))
	}
	return stateType(typ)
}

func (l *lowerer) nullableSlice(typ ir.Type) bool {
	return typ.SliceElem() != "" && (l.nullableSlices || l.hasCapacity(typ))
}

func (l *lowerer) sliceList(value *sourceValue) ir.Expr {
	return l.sliceElements(l.value(value), value.Type.Model)
}

func (l *lowerer) sliceElements(value ir.Expr, typ ir.Type) ir.Expr {
	if l.hasCapacity(typ) {
		return ir.PairField{Value: ir.OptionGetD{Value: value, Default: emptyCapacitySlice()}}
	}
	if l.nullableSlice(typ) {
		return ir.OptionGetD{Value: value, Default: ir.EmptySlice{}}
	}
	return value
}

func emptyCapacitySlice() ir.Expr {
	return ir.Pair{Left: ir.EmptySlice{}, Right: ir.NatZero{}}
}

func (l *lowerer) freshSlice(elements ir.Expr, typ ir.Type) ir.Expr {
	if l.hasCapacity(typ) {
		return ir.Some{Value: ir.Pair{Left: elements, Right: ir.ListLength{List: elements}}}
	}
	if l.nullableSlice(typ) {
		return ir.Some{Value: elements}
	}
	return elements
}

func (l *lowerer) typeSymbol(t *sourceType, suffix string) ir.Symbol {
	symbol := ir.Symbol{Package: l.root, File: l.file, Name: t.Name + suffix}
	if t.Package != l.root {
		symbol.Dependency = t.Package
	}
	return symbol
}

func (l *lowerer) useContract(t *sourceType, handle ir.Type) {
	l.usedContracts[handle] = true
	if _, exists := l.contracts[handle]; exists {
		return
	}
	contract := ir.Contract{Symbol: l.typeSymbol(t, "Contract"), Laws: t.Laws}
	for _, method := range t.Methods {
		field := ir.Method{Name: method.Name}
		for _, param := range method.Params {
			field.Params = append(field.Params, l.ordinaryType(param))
		}
		if method.Result == t {
			field.Result = handle
		} else {
			field.Result = l.ordinaryType(method.Result)
		}
		contract.Methods = append(contract.Methods, field)
	}
	l.contracts[handle] = contract
}

func (l *lowerer) load(addr *sourceValue) ir.Expr {
	if addr.Kind == indexAddress && addr.X.ArrayInitial == nil && addr.X.Type.Elem != nil {
		if elem, _ := addr.X.Type.Elem.Model.ArrayShape(); elem != "" {
			return ir.ArrayGet{Sequence: l.load(addr.X), Index: l.value(addr.IndexValue),
				IndexType: l.valueType(addr.IndexValue.Type), Default: l.zeroValue(addr.Type.Elem)}
		}
	}
	if addr.ArrayInitial != nil {
		return l.value(addr.ArrayInitial)
	}
	if addr.Kind == fieldAddress {
		if addr.ReadOnly {
			return l.value(addr)
		}
		return ir.RecordField{Value: l.load(addr.X), Name: addr.Field}
	}
	if addr.HasCell {
		if addr.MutableCell {
			return l.value(addr)
		}
		if addr.RecordWhole != nil {
			return l.value(addr.RecordWhole)
		}
		value := ir.RecordLiteral{Type: l.valueType(addr.Type.Elem)}
		for _, field := range addr.RecordFields {
			value.Values = append(value.Values, l.value(field))
		}
		return value
	}
	return l.value(addr)
}

func (l *lowerer) captureType(value *sourceValue) ir.Type {
	typ := value.Capture
	l.usesWord = l.usesWord || typ.IsWord()
	return typ
}

func (l *lowerer) recordStore(addr *sourceValue, value ir.Expr) ir.Expr {
	if addr.Kind == indexAddress {
		update := ir.ArraySet{Sequence: l.load(addr.X), Index: l.value(addr.IndexValue),
			IndexType: l.valueType(addr.IndexValue.Type), Value: value}
		return l.recordStore(addr.X, update)
	}
	if addr.Kind != fieldAddress {
		return value
	}
	update := ir.RecordUpdate{Record: l.load(addr.X), Field: addr.Field, Value: value}
	return l.recordStore(addr.X, update)
}

func (l *lowerer) zeroValue(t *sourceType) ir.Expr {
	typ := l.valueType(t)
	if elem, length := typ.ArrayShape(); elem != "" {
		return ir.ArrayReplicate{Length: length, Value: l.zeroValue(t.Elem)}
	}
	if typ.SliceElem() != "" {
		return ir.NilPointer{}
	}
	switch typ {
	case ir.Error:
		return ir.NilPointer{}
	case ir.Bool:
		return ir.BoolLiteral(false)
	case ir.Bytes:
		return ir.BytesLiteral("")
	case ir.Float32:
		return ir.Float32Literal(0)
	case ir.Float64:
		return ir.Float64Literal(0)
	}
	if t.IsRecord {
		zero := ir.RecordLiteral{Type: typ}
		for _, field := range t.Fields {
			zero.Values = append(zero.Values, l.zeroValue(field.Type))
		}
		return zero
	}
	return ir.IntLiteral{Type: typ, Value: "0"}
}

func (l *lowerer) sliceCallback(value *sourceValue, effectful bool) ir.Expr {
	fn := value.Target
	var captures []ir.Expr
	if value.Kind == closureValue {
		for _, capture := range value.Values {
			captures = append(captures, l.value(capture))
		}
	}
	contracts := l.facts.contracts(fn)
	for _, contract := range contracts {
		l.usedContracts[contract] = true
	}
	var callback ir.Expr = ir.Call{Callee: l.symbol(fn), Contracts: contracts, Args: captures}
	if effectful && !l.facts.effect(fn) {
		callback = ir.LiftCallback{Function: callback}
	}
	return callback
}

func (l *lowerer) lowerStructuredFold(fold *sourceRange) ir.StructuredFold {
	spec := fold.Structured
	iter := spec.Iteration
	sequence := l.sliceList(fold.Source)
	initial := func(value *sourceValue) ir.Expr {
		if value == fold.AppendTo {
			return ir.Some{Value: ir.Pair{Left: ir.EmptySlice{}, Right: ir.ListLength{List: sequence}}}
		}
		return l.value(value)
	}
	result := ir.StructuredFold{Sequence: sequence, Initial: packResults(spec.Initial, initial), Element: l.bind(fold.Element)}
	typ := l.loopStateType(spec.States)
	result.State = l.freshBinder("state", typ)
	bindings := l.unpackLoopState(spec.States, result.State)
	result.Final = l.freshBinder("final", typ)
	l.iteration = &iteration{header: iter.Header, skip: iter.Skip, backValues: spec.Next}
	parameterBindings := l.state
	result.Iteration = l.body(iter.Entry, iter.Header)
	result.Iteration.Bindings = append(bindings, result.Iteration.Bindings...)
	result.Effectful = l.canPanic
	l.iteration = nil
	l.state = restoreBindings(parameterBindings, l.state)
	result.Continuation = l.body(spec.Exit, iter.Header)
	result.Continuation.Bindings = append(l.unpackLoopState(spec.States, result.Final), result.Continuation.Bindings...)
	return result
}

func (l *lowerer) freshBinder(name string, typ ir.Type) ir.Binder {
	binder := ir.Binder{Index: int(l.state.NextID()), Name: name, Type: typ}
	l.state = l.state.Advance()
	return binder
}

func (l *lowerer) loopStateType(states []*sourceValue) ir.Type {
	last := len(states) - 1
	typ := l.ordinaryType(states[last].Type)
	for i := last - 1; i >= 0; i-- {
		typ = ir.ProductType(l.ordinaryType(states[i].Type), typ)
	}
	return typ
}

func (l *lowerer) unpackLoopState(states []*sourceValue, state ir.Binder) []ir.Binding {
	var bindings []ir.Binding
	var tuple ir.Expr = ir.Ref(state)
	for i, phi := range states {
		value := tuple
		if i < len(states)-1 {
			value = ir.PairField{Value: tuple}
			tuple = ir.PairField{Value: tuple, Second: true}
		}
		binder, ok := l.binding(phi)
		if !ok {
			binder = l.bind(phi)
		}
		bindings = append(bindings, ir.Binding{Binder: binder, Value: value})
	}
	return bindings
}

func (l *lowerer) lowerStructuredCountedLoop(fn *ir.Function, loop *sourceCounted) {
	spec := loop.Structured
	iter := spec.Iteration
	typ := l.loopStateType(spec.States)
	helper := ir.CountedLoop{Symbol: fn.Symbol, State: l.freshBinder("state", typ)}
	helper.Symbol.Name += "$loop"
	helper.Params = slices.Clone(fn.Params)
	fn.Body.Bindings = l.lowerPureSteps(loop.Before)
	for _, value := range loop.Before {
		helper.Params = append(helper.Params, l.mustBinding(value))
	}
	call := ir.Call{Callee: helper.Symbol}
	for _, param := range helper.Params {
		call.Args = append(call.Args, ir.Ref(param))
	}
	call.Args = append(call.Args, ir.LoopFuel{Start: l.value(loop.Start), Bound: l.value(loop.Bound),
		Signed: !loop.Bound.Type.Model.IsUnsigned(), ZeroStart: loop.Start.IsZero}, packResults(spec.Initial, l.value))
	initialBindings := l.unpackLoopState(spec.States, helper.State)
	wrapperBindings := l.state
	l.iteration = &iteration{header: iter.Header, backValues: spec.Next}
	body := l.body(iter.Entry, iter.Header)
	body.Bindings = append(initialBindings, body.Bindings...)
	helper.Body = &body
	l.iteration = nil
	l.state = restoreBindings(wrapperBindings, l.state)
	final := l.freshBinder("final", typ)
	fn.Body.Bindings = append(fn.Body.Bindings, ir.Binding{Binder: final, Value: call})
	fn.Body.Bindings = append(fn.Body.Bindings, l.unpackLoopState(spec.States, final)...)
	continuation := l.body(spec.Exit, iter.Header)
	fn.Body.Bindings = append(fn.Body.Bindings, continuation.Bindings...)
	fn.Body.Result = continuation.Result
	fn.Loop = &helper
}

func storedValue(stores []*sourceStore, instruction *sourceValue) *sourceValue {
	for _, store := range stores {
		if store.Instruction == instruction {
			return store.Value
		}
	}
	return nil
}

func backEdgeValues(edges []*sourceBackEdge, predecessor *sourceBlock) []*sourceValue {
	for _, edge := range edges {
		if edge.Block == predecessor {
			return edge.Values
		}
	}
	return nil
}
