// Package lower converts checked SSA into structured Lean-ready IR.
package lower

import (
	"go/constant"
	"go/token"
	"go/types"
	"maps"
	"math"
	"net/url"
	"slices"
	"strconv"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/subset"
	"golang.org/x/tools/go/ssa"
)

func FromSSA(checked subset.Checked, sourceStem string, wordBits int64) ir.Program {
	program := ir.Program{Records: make(map[ir.Type]ir.Record), Contracts: make(map[ir.Type]ir.Contract)}
	file := url.PathEscape(sourceStem)
	// The checker orders callees before callers, so their effects are already known.
	effects := make(map[*ssa.Function]bool)
	dependencies := make(map[*ssa.Function][]ir.Type)
	instances := make(map[*ssa.Function]string)
	for _, fn := range checked.Functions() {
		if len(fn.TypeArgs()) != 0 {
			instances[fn] = fn.Origin().Name() + "$instance" + strconv.Itoa(len(instances))
		}
		l := lowerer{
			root: checked.Root(), file: file, bindings: make(map[ssa.Value]ir.Binder), effects: effects,
			checked: checked, records: program.Records, instances: instances,
			contracts: program.Contracts, dependencies: dependencies, usedContracts: make(map[ir.Type]bool),
		}
		result := ir.Function{Symbol: l.symbol(fn), Result: l.valueType(fn.Signature.Results().At(0).Type())}
		for i := 0; i < fn.Signature.TypeParams().Len(); i++ {
			result.TypeParams = append(result.TypeParams, ir.TypeParameter(i))
		}
		for _, capture := range fn.FreeVars {
			result.Params = append(result.Params, l.bindAs(capture, l.captureType(capture)))
		}
		chain := checked.ChainRecursion(fn)
		for _, param := range fn.Params {
			if build := checked.SliceBuild(fn); build != nil && param == build.Callback {
				result.Params = append(result.Params, l.bindAs(param, build.CallbackType()))
			} else if chain != nil && param == chain.Input {
				result.Params = append(result.Params, l.bindAs(param, ir.SliceType(ir.Int64)))
			} else {
				result.Params = append(result.Params, l.bind(param))
			}
		}
		if loop := checked.CountedLoop(fn); loop != nil {
			l.lowerCountedLoop(&result, loop)
		} else if fold := checked.RangeFold(fn); fold != nil {
			result.Body.Result = l.lowerRangeFold(fold)
		} else if build := checked.SliceBuild(fn); build != nil {
			result.Body.Result = l.lowerSliceBuild(build)
		} else if chain != nil {
			result.Body.Result = l.lowerChainRecursion(chain)
		} else {
			result.Body = l.body(fn.Blocks[0], nil)
		}
		if l.usesWord {
			program.WordBits = wordBits
		}
		result.Contracts = slices.Sorted(maps.Keys(l.usedContracts))
		dependencies[fn] = result.Contracts
		result.CanPanic = l.canPanic
		effects[fn] = result.CanPanic
		program.Functions = append(program.Functions, result)
	}
	return program
}

func (l *lowerer) lowerCountedLoop(fn *ir.Function, loop *subset.CountedLoop) {
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
	helper.Next = l.value(loop.Next)
	call.Args = append(call.Args, ir.ToNat{Value: l.value(loop.Bound)}, l.value(loop.Initial))
	fn.Body.Result = ir.Return{Value: call}
	fn.Loop = &helper
}

func (l *lowerer) lowerRangeFold(fold *subset.RangeFold) ir.ListFold {
	result := ir.ListFold{
		Sequence: l.value(fold.Source), Initial: l.value(fold.Initial),
		State: l.bind(fold.State), Element: l.bind(fold.Element),
	}
	result.Steps = l.lowerPureSteps(fold.Steps)
	result.Next = l.value(fold.Next)
	return result
}

func (l *lowerer) lowerSliceBuild(build *subset.SliceBuild) ir.ListBuild {
	l.canPanic = true // Keep the checked construction in the panic-result model.
	result := ir.ListBuild{Sequence: l.value(build.Source), Element: l.bind(build.Element)}
	result.Steps = l.lowerPureSteps(build.Steps)
	result.Next = l.value(build.Value)
	return result
}

func (l *lowerer) lowerChainRecursion(chain *subset.ChainRecursion) ir.ListRecursion {
	input := l.bindings[chain.Input]
	result := ir.ListRecursion{Input: input, Tail: l.bindAs(chain.Tail, input.Type), Base: l.value(chain.Base)}
	if chain.Head != nil {
		head := l.bind(chain.Head)
		result.Head = &head
	}
	result.Step.Bindings = l.lowerPureSteps(chain.Steps)
	result.Step.Result = ir.Return{Value: l.value(chain.Result)}
	return result
}

func (l *lowerer) lowerPureSteps(values []ssa.Value) []ir.Binding {
	var steps []ir.Binding
	for _, step := range values {
		var expr ir.Expr
		switch step := step.(type) {
		case *ssa.BinOp:
			expr = l.binary(step)
		case *ssa.UnOp:
			expr = ir.Negate{Value: l.value(step.X)}
		case *ssa.Call:
			arg := l.value(step.Call.Args[0])
			if callee := step.Call.StaticCallee(); callee != nil {
				expr = ir.SelfCall{Name: l.symbol(callee).Name, Argument: arg}
			} else {
				expr = ir.Apply{Function: l.value(step.Call.Value), Argument: arg}
			}
		}
		steps = append(steps, ir.Binding{Binder: l.bind(step), Value: expr})
	}
	return steps
}

type lowerer struct {
	root          *ssa.Package
	file          string
	bindings      map[ssa.Value]ir.Binder
	effects       map[*ssa.Function]bool
	canPanic      bool
	next          int
	usesWord      bool
	checked       subset.Checked
	records       map[ir.Type]ir.Record
	instances     map[*ssa.Function]string
	contracts     map[ir.Type]ir.Contract
	dependencies  map[*ssa.Function][]ir.Type
	usedContracts map[ir.Type]bool
}

func (l *lowerer) symbol(fn *ssa.Function) ir.Symbol {
	symbol := ir.Symbol{Package: l.root.Pkg.Path(), File: l.file, Name: fn.Name()}
	if recv := fn.Signature.Recv(); recv != nil {
		typ := types.Unalias(recv.Type())
		if pointer, ok := typ.(*types.Pointer); ok {
			typ = types.Unalias(pointer.Elem())
		}
		symbol.Name = typ.(*types.Named).Obj().Name() + "$" + fn.Name()
	}
	pkg := fn.Pkg
	if name, ok := l.instances[fn]; ok {
		symbol.Name = name
		pkg = fn.Origin().Pkg
	}
	if pkg != l.root {
		symbol.Dependency = pkg.Pkg.Path()
	}
	return symbol
}

func (l *lowerer) bind(value ssa.Value) ir.Binder {
	return l.bindAs(value, l.valueType(value.Type()))
}

func (l *lowerer) bindAs(value ssa.Value, typ ir.Type) ir.Binder {
	binder := ir.Binder{Name: value.Name(), Index: l.next, Type: typ}
	l.next++
	l.bindings[value] = binder
	return binder
}

func (l *lowerer) body(block, predecessor *ssa.BasicBlock) ir.Body {
	var result ir.Body
	for _, ins := range block.Instrs {
		switch ins := ins.(type) {
		case *ssa.BinOp:
			canPanic := ins.Op == token.QUO
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins), Value: l.binary(ins), CanPanic: canPanic,
			})
			l.canPanic = l.canPanic || canPanic
		case *ssa.UnOp:
			var value ir.Expr
			canPanic := false
			switch ins.Op {
			case token.NOT:
				value = ir.Not{Value: l.value(ins.X)}
			case token.MUL:
				canPanic = subset.IsReadOnlyRecordPointer(ins.X)
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
		case *ssa.Field:
			record := ins.X.Type().Underlying().(*types.Struct)
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins),
				Value:  ir.RecordField{Value: l.value(ins.X), Name: record.Field(ins.Field).Name()},
			})
		case *ssa.FieldAddr:
			if subset.IsReadOnlyRecordField(ins) {
				recordType := ins.X.Type().Underlying().(*types.Pointer).Elem()
				field := recordType.Underlying().(*types.Struct).Field(ins.Field)
				binder := l.bindAs(ins, l.valueType(field.Type()))
				source := l.value(ins.X)
				_, nested := ins.X.(*ssa.FieldAddr)
				var value ir.Expr = ir.RecordField{Value: source, Name: field.Name()}
				if !nested {
					value = ir.CheckedRecordField{Value: source, Type: l.valueType(recordType), Name: field.Name()}
					l.canPanic = true
				}
				result.Bindings = append(result.Bindings, ir.Binding{
					Binder: binder, Value: value, CanPanic: !nested,
				})
			}
		case *ssa.IndexAddr:
			result.Bindings = append(result.Bindings, l.checkedIndex(ins, ins.X, ins.Index))
		case *ssa.Index:
			result.Bindings = append(result.Bindings, l.checkedIndex(ins, ins.X, ins.Index))
		case *ssa.MakeMap:
			l.canPanic = true // Keep the fresh map result in the panic-result model.
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: ir.EmptyMap{}})
		case *ssa.MapUpdate:
			// The checker proved exclusive access, so a new binding can replace
			// the map state without losing observations through other aliases.
			update := ir.MapUpdate{Map: l.value(ins.Map), Key: l.value(ins.Key), Value: l.value(ins.Value)}
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins.Map), Value: update})
		case *ssa.Lookup:
			_, elem := l.valueType(ins.X.Type()).MapShape()
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bindAs(ins, ir.OptionType(elem)),
				Value:  ir.MapLookup{Map: l.value(ins.X), Key: l.value(ins.Index)},
			})
		case *ssa.Extract:
			binder := l.bind(ins)
			lookup := l.value(ins.Tuple)
			var value ir.Expr = ir.OptionIsSome{Value: lookup}
			if ins.Index == 0 {
				value = ir.OptionGetD{Value: lookup, Default: ir.IntLiteral{Value: "0", Type: binder.Type}}
			}
			result.Bindings = append(result.Bindings, ir.Binding{Binder: binder, Value: value})
		case *ssa.Call:
			if ins.Call.IsInvoke() {
				receiver := ins.Call.Value
				call := ir.InterfaceCall{
					Contract: l.valueType(receiver.Type()), Method: ins.Call.Method.Name(),
					Args: []ir.Expr{l.value(receiver)},
				}
				for _, arg := range ins.Call.Args {
					call.Args = append(call.Args, l.value(arg))
				}
				result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: call})
				continue
			}
			if subset.IsLength(ins) {
				result.Bindings = append(result.Bindings, ir.Binding{
					Binder: l.bind(ins), Value: ir.ByteLen{Value: l.value(ins.Call.Args[0])},
				})
				continue
			}
			target := ins.Call.StaticCallee()
			call := ir.Call{Callee: l.symbol(target), Contracts: l.dependencies[target]}
			for _, contract := range call.Contracts {
				l.usedContracts[contract] = true
			}
			if closure, ok := ins.Call.Value.(*ssa.MakeClosure); ok {
				for _, capture := range closure.Bindings {
					call.Args = append(call.Args, l.value(capture))
				}
			}
			for _, arg := range ins.Call.Args {
				call.Args = append(call.Args, l.value(arg))
			}
			canPanic := l.effects[target]
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bind(ins), Value: call, CanPanic: canPanic,
			})
			l.canPanic = l.canPanic || canPanic
		case *ssa.Convert:
			binder := l.bind(ins)
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: binder, Value: ir.Convert{Value: l.value(ins.X), To: binder.Type},
			})
		case *ssa.ChangeType:
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: l.value(ins.X)})
		case *ssa.Store:
			if _, ok := l.checked.RecordCell(ins.Addr); ok {
				continue
			}
			if l.checked.ArrayInitializer(ins.Addr) != nil {
				continue
			}
			if _, ok := ins.Addr.(*ssa.FieldAddr); ok {
				continue
			}
			result.Bindings = append(result.Bindings, ir.Binding{
				Binder: l.bindAs(ins.Addr, l.captureType(ins.Addr)), Value: l.value(ins.Val),
			})
		case *ssa.If:
			result.Result = ir.If{
				Condition: l.value(ins.Cond),
				Then:      l.body(block.Succs[0], block),
				Else:      l.body(block.Succs[1], block),
			}
		case *ssa.Phi:
			// Each branch contains only the computations along its own path.
			edge := ins.Edges[slices.Index(block.Preds, predecessor)]
			result.Bindings = append(result.Bindings, ir.Binding{Binder: l.bind(ins), Value: l.value(edge)})
		case *ssa.Return:
			result.Result = ir.Return{Value: l.value(ins.Results[0])}
		case *ssa.Jump:
			next := l.body(block.Succs[0], block)
			result.Bindings = append(result.Bindings, next.Bindings...)
			result.Result = next.Result
		}
	}
	return result
}

func (l *lowerer) checkedIndex(value, sequence, index ssa.Value) ir.Binding {
	if init := l.checked.ArrayInitializer(sequence); init != nil {
		sequence = init.Val
	}
	typ := l.valueType(sequence.Type())
	elem := typ.SliceElem()
	if elem == "" {
		elem, _ = typ.ArrayShape()
	}
	l.canPanic = true
	return ir.Binding{
		Binder: l.bindAs(value, elem),
		Value: ir.CheckedIndex{
			Sequence: l.value(sequence), SequenceType: typ, Index: l.value(index), IndexType: l.valueType(index.Type()),
		},
		CanPanic: true,
	}
}

func (l *lowerer) value(value ssa.Value) ir.Expr {
	if fn, ok := value.(*ssa.Function); ok {
		return ir.FunctionRef(l.symbol(fn))
	}
	if c, ok := value.(*ssa.Const); ok {
		typ := l.valueType(c.Type())
		if typ.Pointee() != "" {
			return ir.NilPointer{}
		}
		if typ.SliceElem() != "" {
			return ir.EmptySlice{}
		}
		if key, _ := typ.MapShape(); key != "" {
			return ir.EmptyMap{}
		}
		switch typ {
		case ir.Float32:
			f, _ := constant.Float32Val(c.Value)
			return ir.Float32Literal(math.Float32bits(f))
		case ir.Float64:
			f, _ := constant.Float64Val(c.Value)
			return ir.Float64Literal(math.Float64bits(f))
		}
		switch c.Value.Kind() {
		case constant.Bool:
			return ir.BoolLiteral(constant.BoolVal(c.Value))
		case constant.String:
			return ir.BytesLiteral(constant.StringVal(c.Value))
		}
		return ir.IntLiteral{Value: c.Value.ExactString(), Type: typ}
	}
	if binder, ok := l.bindings[value]; ok {
		return ir.Ref(binder)
	}
	panic("missing binding for checked SSA value: " + value.String())
}

func (l *lowerer) binary(expr *ssa.BinOp) ir.Binary {
	op, _ := subset.Binary(expr.Op)
	return ir.Binary{Op: op, Left: l.value(expr.X), Right: l.value(expr.Y), OperandType: l.valueType(expr.X.Type())}
}

func (l *lowerer) valueType(t types.Type) ir.Type {
	if handle := subset.InterfaceHandle(t); handle != "" {
		l.useContract(t, handle)
		return handle
	}
	typ := subset.Type(t)
	l.usesWord = l.usesWord || typ.IsWord()
	if typ.Pointee() != "" {
		l.valueType(t.Underlying().(*types.Pointer).Elem())
	}
	if typ.SliceElem() != "" {
		l.valueType(t.Underlying().(*types.Slice).Elem())
	}
	if elem, _ := typ.ArrayShape(); elem != "" {
		l.valueType(t.Underlying().(*types.Array).Elem())
	}
	if key, value := typ.MapShape(); key != "" {
		l.usesWord = l.usesWord || key.IsWord() || value.IsWord()
	}
	if typ.IsRecord() {
		if _, exists := l.records[typ]; !exists {
			named := types.Unalias(t).(*types.Named)
			obj := named.Obj()
			symbol := ir.Symbol{Package: l.root.Pkg.Path(), File: l.file, Name: obj.Name()}
			if obj.Pkg() != l.root.Pkg {
				symbol.Dependency = obj.Pkg().Path()
			}
			var fields []ir.Field
			for field := range named.Underlying().(*types.Struct).Fields() {
				fields = append(fields, ir.Field{Name: field.Name(), Type: l.valueType(field.Type())})
			}
			l.records[typ] = ir.Record{Symbol: symbol, Fields: fields}
		}
	}
	return typ
}

func (l *lowerer) useContract(t types.Type, handle ir.Type) {
	l.usedContracts[handle] = true
	if _, exists := l.contracts[handle]; exists {
		return
	}
	named := types.Unalias(t).(*types.Named)
	obj := named.Obj()
	symbol := ir.Symbol{Package: l.root.Pkg.Path(), File: l.file, Name: obj.Name() + "Contract"}
	if obj.Pkg() != l.root.Pkg {
		symbol.Dependency = obj.Pkg().Path()
	}
	contract := ir.Contract{Symbol: symbol, Laws: l.checked.InterfaceLaws(t)}
	for method := range named.Underlying().(*types.Interface).ExplicitMethods() {
		sig := method.Signature()
		field := ir.Method{Name: method.Name()}
		for param := range sig.Params().Variables() {
			field.Params = append(field.Params, l.valueType(param.Type()))
		}
		if result := sig.Results().At(0).Type(); types.Identical(result, t) {
			field.Result = handle
		} else {
			field.Result = l.valueType(result)
		}
		contract.Methods = append(contract.Methods, field)
	}
	l.contracts[handle] = contract
}

func (l *lowerer) load(addr ssa.Value) ir.Expr {
	if init := l.checked.ArrayInitializer(addr); init != nil {
		return l.value(init.Val)
	}
	if field, ok := addr.(*ssa.FieldAddr); ok {
		if subset.IsReadOnlyRecordField(field) {
			return l.value(field)
		}
		record := field.X.Type().Underlying().(*types.Pointer).Elem().Underlying().(*types.Struct)
		return ir.RecordField{Value: l.load(field.X), Name: record.Field(field.Field).Name()}
	}
	if cell, ok := l.checked.RecordCell(addr); ok {
		if cell.Whole != nil {
			return l.value(cell.Whole.Val)
		}
		typ := l.valueType(addr.Type().Underlying().(*types.Pointer).Elem())
		value := ir.RecordLiteral{Type: typ}
		for _, field := range cell.Fields {
			value.Values = append(value.Values, l.value(field.Val))
		}
		return value
	}
	// Validated capture loads read a value already bound by the initializer.
	return l.value(addr)
}

func (l *lowerer) captureType(value ssa.Value) ir.Type {
	typ := subset.CaptureType(value.Type())
	l.usesWord = l.usesWord || typ.IsWord()
	return typ
}
