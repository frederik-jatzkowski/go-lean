package lower

import (
	"go/constant"
	"go/token"
	"go/types"
	"math"
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/subset"
	"golang.org/x/tools/go/ssa"
)

// NewInput snapshots checked SSA into the scalar view consumed by FromSSA.
func NewInput(checked subset.Checked) Input {
	builder := ssaInputBuilder{checked: checked, functions: make(map[*ssa.Function]*sourceFunction),
		blocks: make(map[*ssa.BasicBlock]*sourceBlock), values: make(map[any]*sourceValue),
		types: make(map[types.Type]*sourceType), positions: make(map[*ssa.BasicBlock]map[ssa.Instruction]int)}
	p := &sourceProgram{}
	if root := checked.Root(); root != nil {
		p.Package = root.Pkg.Path()
	}
	for _, fn := range checked.Functions() {
		p.Functions = append(p.Functions, builder.function(fn))
	}
	for _, fn := range checked.Functions() {
		builder.fillFunction(fn)
	}
	return newInputGraph(p)
}

type ssaInputBuilder struct {
	checked   subset.Checked
	functions map[*ssa.Function]*sourceFunction
	blocks    map[*ssa.BasicBlock]*sourceBlock
	values    map[any]*sourceValue
	types     map[types.Type]*sourceType
	positions map[*ssa.BasicBlock]map[ssa.Instruction]int
}

func mapped[A, B any](items []A, convert func(A) B) []B {
	var result []B
	for _, item := range items {
		result = append(result, convert(item))
	}
	return result
}

func (b *ssaInputBuilder) function(fn *ssa.Function) *sourceFunction {
	if fn == nil {
		return nil
	}
	if current := b.functions[fn]; current != nil {
		return current
	}
	f := &sourceFunction{Name: fn.Name()}
	b.functions[fn] = f
	pkg := fn.Pkg
	if len(fn.TypeArgs()) != 0 {
		f.Origin = fn.Origin().Name()
		pkg = fn.Origin().Pkg
	}
	if pkg != nil {
		f.Package = pkg.Pkg.Path()
	}
	if recv := fn.Signature.Recv(); recv != nil {
		t := types.Unalias(recv.Type())
		if p, ok := t.(*types.Pointer); ok {
			t = types.Unalias(p.Elem())
		}
		if named, ok := t.(*types.Named); ok {
			f.Receiver = named.Obj().Name()
		}
	}
	f.TypeParameters = fn.Signature.TypeParams().Len()
	f.Results = b.tuple(fn.Signature.Results())
	return f
}

func (b *ssaInputBuilder) fillFunction(fn *ssa.Function) {
	f := b.function(fn)
	f.Params = mapped(fn.Params, func(p *ssa.Parameter) *sourceValue { return b.value(p) })
	f.FreeVars = mapped(fn.FreeVars, func(v *ssa.FreeVar) *sourceValue { return b.value(v) })
	if len(fn.Blocks) > 0 {
		f.Entry = b.block(fn.Blocks[0])
	}
	if m := b.checked.Stateful(fn); m != nil {
		f.Stateful = &sourceStateful{Receiver: b.value(m.Receiver), Record: b.typ(subset.StatefulRecord(m.Receiver.Type()))}
		if m.Callback != nil {
			f.Stateful.Callback = b.value(m.Callback)
			f.Stateful.CallbackInput = b.typ(subset.BooleanCallbackInput(m.Callback.Type()))
		}
		if m.Loop != nil {
			f.Stateful.Loop = &sourceIndexed{Header: b.block(m.Loop.Header), Sequence: b.value(m.Loop.Sequence), Cursor: b.value(m.Loop.Cursor)}
		}
	}
	if l := b.checked.CountedLoop(fn); l != nil {
		f.Counted = &sourceCounted{Initial: b.value(l.Initial), Next: b.value(l.Next), Start: b.value(l.Start),
			Bound: b.value(l.Bound), Result: b.value(l.Result), Steps: b.valuesOf(l.Steps), Before: b.valuesOf(l.Before),
			After: b.valuesOf(l.After), Structured: b.loop(l.Structured), Control: l.Control, RangeGuard: l.RangeGuard}
		if l.State != nil {
			f.Counted.State = b.value(l.State)
		}
	}
	if l := b.checked.RangeFold(fn); l != nil {
		f.Range = &sourceRange{Initial: b.value(l.Initial), Next: b.value(l.Next), Source: b.value(l.Source),
			Steps: b.valuesOf(l.Steps), Structured: b.loop(l.Structured), Excluded: b.value(l.Excluded), Prelude: b.block(l.Prelude)}
		if l.AppendTo != nil {
			f.Range.AppendTo = b.value(l.AppendTo)
		}
		if l.Element != nil {
			f.Range.Element = b.value(l.Element)
		}
		if l.State != nil {
			f.Range.State = b.value(l.State)
		}
	}
	if l := b.checked.SliceBuild(fn); l != nil {
		f.Build = &sourceBuild{Exit: b.block(l.Exit), ExitStart: l.ExitStart, Source: b.value(l.Source),
			Lengths: mapped(l.Lengths, func(c *ssa.Call) *sourceValue { return b.value(c) }),
			Steps:   b.valuesOf(l.Steps), Value: b.value(l.Value), Effectful: l.Effectful, Iteration: b.iteration(l.Iteration)}
		if l.Element != nil {
			f.Build.Element = b.value(l.Element)
		}
		if l.Copy != nil {
			f.Build.Copy = b.value(l.Copy)
		}
		if l.Destination != nil {
			f.Build.Destination = b.value(l.Destination)
		}
		if l.Callback != nil {
			f.Build.Callback, f.Build.CallbackType = b.value(l.Callback), l.CallbackType()
		}
	}
	if c := b.checked.ChainRecursion(fn); c != nil {
		f.Chain = &sourceChain{Input: b.value(c.Input), Tail: b.value(c.Tail), Element: c.Element, Base: b.valuesOf(c.Base),
			Steps: b.valuesOf(c.Steps), Result: b.valuesOf(c.Result)}
		if c.Head != nil {
			f.Chain.Head = b.value(c.Head)
		}
	}
}

func (b *ssaInputBuilder) loop(loop *subset.LoopState) *sourceLoop {
	if loop == nil {
		return nil
	}
	result := &sourceLoop{Iteration: b.iteration(loop.Iteration), Exit: b.block(loop.Exit), Initial: b.valuesOf(loop.Initial),
		States: mapped(loop.States, func(p *ssa.Phi) *sourceValue { return b.value(p) })}
	blocks := make([]*ssa.BasicBlock, 0, len(loop.Next))
	for block := range loop.Next {
		blocks = append(blocks, block)
	}
	slices.SortFunc(blocks, func(a, b *ssa.BasicBlock) int { return a.Index - b.Index })
	for _, block := range blocks {
		result.Next = append(result.Next, &sourceBackEdge{Block: b.block(block), Values: b.valuesOf(loop.Next[block])})
	}
	return result
}

func (b *ssaInputBuilder) iteration(iter *subset.TraversalIteration) *sourceIteration {
	if iter == nil {
		return nil
	}
	result := &sourceIteration{Entry: b.block(iter.Entry), Header: b.block(iter.Header)}
	// Read matches in source block and instruction order.
	for _, block := range iter.Header.Parent().Blocks {
		for _, ins := range block.Instrs {
			if iter.Skip[ins] {
				result.Skip = append(result.Skip, b.instruction(ins))
			}
			if value := iter.Stores[ins]; value != nil {
				result.Stores = append(result.Stores, &sourceStore{Instruction: b.instruction(ins), Value: b.value(value)})
			}
		}
	}
	return result
}

func (b *ssaInputBuilder) block(block *ssa.BasicBlock) *sourceBlock {
	if block == nil {
		return nil
	}
	if current := b.blocks[block]; current != nil {
		return current
	}
	result := &sourceBlock{}
	b.blocks[block] = result
	result.Instructions = mapped(block.Instrs, b.instruction)
	result.Preds = mapped(block.Preds, b.block)
	result.Succs = mapped(block.Succs, b.block)
	return result
}

func (b *ssaInputBuilder) tuple(t *types.Tuple) []*sourceType {
	var tuple []*sourceType
	for field := range t.Variables() {
		tuple = append(tuple, b.typ(field.Type()))
	}
	return tuple
}

func (b *ssaInputBuilder) typ(t types.Type) *sourceType {
	if t == nil {
		return nil
	}
	t = types.Unalias(t)
	if current := b.types[t]; current != nil {
		return current
	}
	model := subset.Type(t)
	handle := subset.InterfaceHandle(t)
	if handle != "" {
		model = handle
	}
	result := &sourceType{Model: model, IsInterface: handle != ""}
	b.types[t] = result
	if n, ok := t.(*types.Named); ok {
		obj := n.Obj()
		result.Name = obj.Name()
		if obj.Pkg() != nil {
			result.Package = obj.Pkg().Path()
		}
	}
	switch typ := t.Underlying().(type) {
	case *types.Tuple:
		result.IsTuple, result.Tuple = true, b.tuple(typ)
	case *types.Pointer:
		result.Elem = b.typ(typ.Elem())
	case *types.Array:
		result.Elem = b.typ(typ.Elem())
	case *types.Slice:
		result.Elem = b.typ(typ.Elem())
	case *types.Struct:
		result.IsRecord = true
		for field := range typ.Fields() {
			result.Fields = append(result.Fields, &sourceField{Name: field.Name(), Type: b.typ(field.Type())})
		}
	case *types.Interface:
		if handle != "" {
			result.Laws = b.checked.InterfaceLaws(t)
			for method := range typ.ExplicitMethods() {
				sig := method.Signature()
				resultType := &sourceType{Model: ir.Unit}
				if sig.Results().Len() == 1 {
					resultType = b.typ(sig.Results().At(0).Type())
				}
				result.Methods = append(result.Methods, &sourceMethod{Name: method.Name(), Params: b.tuple(sig.Params()), Result: resultType})
			}
		}
	}
	return result
}

func (b *ssaInputBuilder) valuesOf(values []ssa.Value) []*sourceValue { return mapped(values, b.value) }

func (b *ssaInputBuilder) value(val ssa.Value) *sourceValue {
	if val == nil {
		return nil
	}
	if ins, ok := val.(ssa.Instruction); ok {
		return b.instruction(ins)
	}
	if current := b.values[val]; current != nil {
		return current
	}
	result := &sourceValue{Name: val.Name()}
	b.values[val] = result
	b.fillValue(result, val)
	if fn, ok := val.(*ssa.Function); ok {
		result.Kind, result.Target = functionValue, b.function(fn)
	}
	if c, ok := val.(*ssa.Const); ok {
		result.Kind, result.IsNil, result.IsZero = constantValue, c.Value == nil, subset.IsZero(c)
		if c.Value == nil {
			return result
		}
		switch result.Type.Model {
		case ir.Float32:
			f, _ := constant.Float32Val(c.Value)
			result.Bits = uint64(math.Float32bits(f))
		case ir.Float64:
			f, _ := constant.Float64Val(c.Value)
			result.Bits = math.Float64bits(f)
		default:
			switch c.Value.Kind() {
			case constant.Bool:
				result.Boolean = constant.BoolVal(c.Value)
			case constant.String:
				result.Text = constant.StringVal(c.Value)
			default:
				result.Text = c.Value.ExactString()
			}
		}
	}
	return result
}

func (b *ssaInputBuilder) fillValue(result *sourceValue, val ssa.Value) {
	result.Name, result.Type, result.Capture = val.Name(), b.typ(val.Type()), subset.CaptureType(val.Type())
	if init := b.checked.ArrayInitializer(val); init != nil {
		result.ArrayInitial = b.value(init.Val)
	}
	if cell, ok := b.checked.RecordCell(val); ok {
		result.HasCell, result.MutableCell = true, cell.Mutable
		if cell.Whole != nil {
			result.RecordWhole = b.value(cell.Whole.Val)
		}
		for index, field := range cell.Fields {
			if field != nil {
				result.RecordFields = append(result.RecordFields, b.value(field.Val))
			} else if cell.Whole == nil {
				fieldType := val.Type().Underlying().(*types.Pointer).Elem().Underlying().(*types.Struct).Field(index).Type()
				result.RecordFields = append(result.RecordFields, b.value(ssa.NewConst(nil, fieldType)))
			}
		}
	}
}

func (b *ssaInputBuilder) instruction(ins ssa.Instruction) *sourceValue {
	if current := b.values[ins]; current != nil {
		return current
	}
	v := &sourceValue{}
	b.values[ins] = v
	if _, isPhi := ins.(*ssa.Phi); !isPhi {
		var operands [8]*ssa.Value
		for _, operand := range ins.Operands(operands[:0]) {
			if operand != nil && *operand != nil {
				v.Operands = append(v.Operands, &sourceOperand{
					Value: b.value(*operand), Dominates: b.operandDominates(*operand, ins),
				})
			}
		}
	}
	if val, ok := ins.(ssa.Value); ok {
		b.fillValue(v, val)
	}
	switch i := ins.(type) {
	case *ssa.BinOp:
		v.Kind, v.X, v.Y = binaryValue, b.value(i.X), b.value(i.Y)
		v.Op, _ = subset.Binary(i.Op)
	case *ssa.UnOp:
		v.Kind, v.X, v.Not, v.Dereference = unaryValue, b.value(i.X), i.Op == token.NOT, i.Op == token.MUL
		v.ReadOnly = v.Dereference && subset.IsReadOnlyRecordPointer(i.X)
	case *ssa.Field:
		f := i.X.Type().Underlying().(*types.Struct).Field(i.Field)
		v.Kind, v.X, v.Field, v.FieldType = fieldValue, b.value(i.X), f.Name(), b.typ(f.Type())
	case *ssa.FieldAddr:
		t := i.X.Type().Underlying().(*types.Pointer).Elem()
		f := t.Underlying().(*types.Struct).Field(i.Field)
		v.Kind, v.X, v.Field, v.FieldType = fieldAddress, b.value(i.X), f.Name(), b.typ(f.Type())
		v.RecordType, v.ReadOnly = b.typ(t), subset.IsReadOnlyRecordField(i)
	case *ssa.IndexAddr:
		v.Kind, v.X, v.IndexValue = indexAddress, b.value(i.X), b.value(i.Index)
		v.IndexInBounds = subset.ArrayIndexInBounds(i.X, i.Index, i)
	case *ssa.Index:
		v.Kind, v.X, v.IndexValue = indexValue, b.value(i.X), b.value(i.Index)
		v.IndexInBounds = subset.ArrayIndexInBounds(i.X, i.Index, i)
	case *ssa.Slice:
		v.Kind = emptySliceValue
		if subset.IsStringSlice(i) {
			v.Kind, v.X, v.Y, v.IndexValue = stringSliceValue, b.value(i.X), b.value(i.Low), b.value(i.High)
		}
	case *ssa.MakeInterface:
		v.Kind, v.Text = concreteErrorValue, subset.ConcreteErrorType(i)
	case *ssa.MakeMap:
		v.Kind = makeMap
	case *ssa.MapUpdate:
		v.Kind, v.X, v.Key, v.Value = mapUpdate, b.value(i.Map), b.value(i.Key), b.value(i.Value)
	case *ssa.Lookup:
		v.Kind, v.X, v.IndexValue, v.CommaOK = mapLookup, b.value(i.X), b.value(i.Index), i.CommaOk
	case *ssa.Extract:
		v.Kind, v.X, v.OperandIndex = extractValue, b.value(i.Tuple), i.Index
	case *ssa.Call:
		if fold := b.checked.RangeFold(i.Parent()); fold != nil {
			if element := fold.Appends[i]; element != nil {
				v.Kind, v.X, v.Y = appendValue, b.value(i.Call.Args[0]), b.value(element)
				break
			}
		}
		v.Kind, v.Call = callValue, &sourceCall{Args: b.valuesOf(i.Call.Args), Value: b.value(i.Call.Value),
			Target: b.function(i.Call.StaticCallee()), Length: subset.IsLength(i), Clone: subset.IsSliceClone(i),
			Extremum: subset.IntegerExtremum(i), Capacity: subset.IsSliceCapacity(i)}
		if i.Call.IsInvoke() {
			v.Call.Method = i.Call.Method.Name()
		}
	case *ssa.Convert:
		v.Kind, v.X = convertValue, b.value(i.X)
	case *ssa.ChangeType:
		v.Kind, v.X = changeType, b.value(i.X)
	case *ssa.Alloc:
		v.Kind = allocValue
	case *ssa.Store:
		v.Kind, v.X, v.Value = storeValue, b.value(i.Addr), b.value(i.Val)
	case *ssa.If:
		v.Kind, v.X = ifValue, b.value(i.Cond)
	case *ssa.Phi:
		v.Kind, v.Values = phiValue, b.valuesOf(i.Edges)
	case *ssa.Return:
		v.Kind, v.Values = returnValue, b.valuesOf(i.Results)
	case *ssa.Jump:
		v.Kind = jumpValue
	case *ssa.MakeClosure:
		fn, _ := i.Fn.(*ssa.Function)
		v.Kind, v.Target, v.Values = closureValue, b.function(fn), b.valuesOf(i.Bindings)
	}
	return v
}

func (b *ssaInputBuilder) operandDominates(operand ssa.Value, use ssa.Instruction) bool {
	definition, ok := operand.(ssa.Instruction)
	if !ok {
		return true // Parameters, captures and literals have no instruction definition.
	}
	def, block := definition.Block(), use.Block()
	if def != block {
		return def != nil && block != nil && def.Parent() == block.Parent() && def.Dominates(block)
	}
	if block == nil {
		return false
	}
	positions := b.positions[block]
	if positions == nil {
		positions = make(map[ssa.Instruction]int, len(block.Instrs))
		for i, ins := range block.Instrs {
			positions[ins] = i
		}
		b.positions[block] = positions
	}
	definitionPosition, known := positions[definition]
	usePosition, found := positions[use]
	return known && found && definitionPosition < usePosition
}
