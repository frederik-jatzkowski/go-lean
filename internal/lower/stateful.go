package lower

import (
	"go/token"
	"go/types"
	"maps"
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/subset"
	"golang.org/x/tools/go/ssa"
)

type statefulLowerer struct {
	*lowerer
	method     *subset.StatefulMethod
	record     ir.Type
	state      ir.Expr
	trace      ir.Expr
	traceType  ir.Type
	loop       ir.Symbol
	loopParams []ir.Expr
	fuel       ir.Expr
}

func stateResult(fn *ssa.Function, state ir.Type) ir.Type {
	value := ir.Unit
	if results := fn.Signature.Results(); results.Len() != 0 {
		value = stateType(subset.Type(results.At(0).Type()))
	}
	return ir.ProductType(state, value)
}

func stateType(typ ir.Type) ir.Type {
	if typ.SliceElem() != "" {
		return ir.OptionType(typ)
	}
	return typ
}

func (l *lowerer) lowerStateful(fn *ssa.Function, method *subset.StatefulMethod) []ir.Function {
	named := subset.StatefulRecord(method.Receiver.Type())
	obj := named.Obj()
	recordType := ir.RecordType(obj.Pkg().Path(), obj.Name())
	recordSymbol := ir.Symbol{Package: l.root.Pkg.Path(), File: l.file, Name: obj.Name()}
	if obj.Pkg() != l.root.Pkg {
		recordSymbol.Dependency = obj.Pkg().Path()
	}
	record := ir.Record{Symbol: recordSymbol}
	for field := range named.Underlying().(*types.Struct).Fields() {
		record.Fields = append(record.Fields, ir.Field{Name: field.Name(), Type: stateType(l.valueType(field.Type()))})
	}
	l.records[recordType] = record

	stateType := ir.OptionType(recordType)
	binder := l.bindAs(method.Receiver, stateType)
	s := statefulLowerer{lowerer: l, method: method, record: recordType, state: ir.Ref(binder)}
	result := ir.Function{Symbol: l.symbol(fn), CanPanic: true, Params: []ir.Binder{binder},
		Result: stateResult(fn, stateType)}
	for _, param := range fn.Params[1:] {
		if param == method.Callback {
			input := l.valueType(subset.BooleanCallbackInput(param.Type()))
			s.traceType = ir.SliceType(input)
			result.Result = ir.ProductType(stateType, ir.ProductType(callbackResult(fn), s.traceType))
			result.Params = append(result.Params, l.bindAs(param, ir.UnaryFunctionType(ir.Nat, ir.UnaryFunctionType(input, ir.Bool))))
		} else {
			result.Params = append(result.Params, s.bind(param))
		}
	}
	s.trace = ir.EmptySlice{}
	if method.Loop == nil {
		result.Body = s.body(fn.Blocks[0], nil)
		return []ir.Function{result}
	}

	loop := ir.Function{Symbol: result.Symbol, Params: slices.Clone(result.Params), Result: result.Result, CanPanic: true}
	loop.Symbol.Name += "$loop"
	s.loop = loop.Symbol
	for _, param := range result.Params[1:] {
		s.loopParams = append(s.loopParams, ir.Ref(param))
	}
	fuel := s.fresh("fuel", ir.Nat)
	loop.Params = append(loop.Params, fuel)
	loop.Fuel = &fuel
	// Lower setup with the caller's state and trace before the recursive helper
	// gets its own fuel and trace parameters.
	result.Body = s.body(fn.Blocks[0], nil)
	if s.traceType != "" {
		trace := s.fresh("trace", s.traceType)
		loop.Params = append(loop.Params, trace)
		s.trace = ir.Ref(trace)
	}
	s.state = ir.Ref(binder)
	s.fuel = ir.Ref(fuel)
	loop.Body = s.body(method.Loop.Header, fn.Blocks[0])
	return []ir.Function{loop, result}
}

func callbackResult(fn *ssa.Function) ir.Type {
	if results := fn.Signature.Results(); results.Len() != 0 {
		return stateType(subset.Type(results.At(0).Type()))
	}
	return ir.Unit
}

func (s *statefulLowerer) bind(value ssa.Value) ir.Binder {
	return s.bindAs(value, stateType(s.valueType(value.Type())))
}

func (s *statefulLowerer) fresh(name string, typ ir.Type) ir.Binder {
	binder := ir.Binder{Name: name, Type: typ, Index: s.next}
	s.next++
	return binder
}

func (s *statefulLowerer) value(value ssa.Value) ir.Expr {
	if c, ok := value.(*ssa.Const); ok && c.Value == nil && subset.Type(c.Type()).SliceElem() != "" {
		return ir.NilPointer{}
	}
	return s.lowerer.value(value)
}

func (s *statefulLowerer) project(addr *ssa.FieldAddr) ir.Expr {
	return ir.CheckedRecordField{Value: s.state, Type: s.record, Name: fieldName(addr)}
}

func fieldName(addr *ssa.FieldAddr) string {
	return addr.X.Type().Underlying().(*types.Pointer).Elem().Underlying().(*types.Struct).Field(addr.Field).Name()
}

func (s *statefulLowerer) length(sequence ir.Expr) ir.Expr {
	s.usesWord = true
	return ir.SliceLength{List: ir.OptionGetD{Value: sequence, Default: ir.EmptySlice{}}}
}

func (s *statefulLowerer) child(block, predecessor *ssa.BasicBlock) ir.Body {
	if s.method.Loop != nil && block == s.method.Loop.Header {
		if s.fuel == nil {
			state := s.fresh("receiver", s.record)
			receiver := ir.Ref(state)
			sequence := ir.RecordField{Value: receiver, Name: fieldName(s.method.Loop.Sequence)}
			cursor := ir.RecordField{Value: receiver, Name: fieldName(s.method.Loop.Cursor)}
			args := append([]ir.Expr{ir.Some{Value: receiver}}, s.loopParams...)
			args = append(args, ir.IndexFuel{Length: s.length(sequence), Cursor: cursor})
			if s.traceType != "" {
				args = append(args, s.trace)
			}
			return ir.Body{Result: ir.WithReceiver{Receiver: s.state, State: state,
				Body: ir.Body{Result: ir.TailCall{Call: ir.Call{Callee: s.loop, Args: args}}}}}
		}
		args := append([]ir.Expr{s.state}, s.loopParams...)
		args = append(args, s.fuel)
		if s.traceType != "" {
			args = append(args, s.trace)
		}
		return ir.Body{Result: ir.TailCall{Call: ir.Call{Callee: s.loop, Args: args}, Recursive: true}}
	}
	child := *s
	lower := *s.lowerer
	lower.bindings = maps.Clone(s.bindings)
	child.lowerer = &lower
	result := child.body(block, predecessor)
	s.usesWord = s.usesWord || child.usesWord
	return result
}

func (s *statefulLowerer) body(block, predecessor *ssa.BasicBlock) ir.Body {
	var body ir.Body
	for _, instruction := range block.Instrs {
		switch ins := instruction.(type) {
		case *ssa.BinOp:
			value := s.binary(ins)
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: value, CanPanic: value.Op.PanicsOnZeroDivisor()})
		case *ssa.FieldAddr:
			if ins.X == s.method.Receiver {
				// Go checks the receiver at address formation, even for a later store.
				binder := s.fresh("receiver", s.record)
				body.Bindings = append(body.Bindings, ir.Binding{Binder: binder, Value: s.state, CanPanic: true})
			}
		case *ssa.UnOp:
			var value ir.Expr
			canPanic := false
			switch ins.Op {
			case token.NOT:
				value = ir.Not{Value: s.value(ins.X)}
			case token.SUB:
				value = ir.Negate{Value: s.value(ins.X)}
			case token.MUL:
				if field, ok := ins.X.(*ssa.FieldAddr); ok && field.X == s.method.Receiver {
					value, canPanic = s.project(field), true
				} else {
					value = s.load(ins.X)
				}
			}
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: value, CanPanic: canPanic})
		case *ssa.IndexAddr:
			typ := s.valueType(ins.X.Type())
			value := ir.CheckedIndex{Sequence: ir.OptionGetD{Value: s.value(ins.X), Default: ir.EmptySlice{}},
				SequenceType: typ, Index: s.value(ins.Index), IndexType: s.valueType(ins.Index.Type())}
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bindAs(ins, typ.SliceElem()), Value: value, CanPanic: true})
		case *ssa.Field:
			field := ins.X.Type().Underlying().(*types.Struct).Field(ins.Field)
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: ir.RecordField{Value: s.value(ins.X), Name: field.Name()}})
		case *ssa.Store:
			if field, ok := ins.Addr.(*ssa.FieldAddr); ok && field.X == s.method.Receiver {
				receiver := s.fresh("receiver", s.record)
				state := s.fresh("state", ir.OptionType(s.record))
				update := ir.RecordUpdate{Record: ir.Ref(receiver), Field: fieldName(field), Value: s.value(ins.Val)}
				body.Bindings = append(body.Bindings, ir.Binding{Binder: receiver, Value: s.state, CanPanic: true},
					ir.Binding{Binder: state, Value: ir.Some{Value: update}})
				s.state = ir.Ref(state)
			}
		case *ssa.Call:
			s.call(&body, ins)
		case *ssa.Convert:
			binder := s.bind(ins)
			body.Bindings = append(body.Bindings, ir.Binding{Binder: binder, Value: ir.Convert{Value: s.value(ins.X), To: binder.Type}})
		case *ssa.ChangeType:
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: s.value(ins.X)})
		case *ssa.Phi:
			edge := ins.Edges[slices.Index(block.Preds, predecessor)]
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: s.value(edge)})
		case *ssa.If:
			body.Result = ir.If{Condition: s.value(ins.Cond), Then: s.child(block.Succs[0], block), Else: s.child(block.Succs[1], block)}
		case *ssa.Jump:
			next := s.child(block.Succs[0], block)
			body.Bindings = append(body.Bindings, next.Bindings...)
			body.Result = next.Result
		case *ssa.Return:
			var value ir.Expr = ir.UnitLiteral{}
			if len(ins.Results) != 0 {
				value = s.value(ins.Results[0])
			}
			if s.traceType != "" {
				value = ir.Pair{Left: value, Right: ir.Reverse{List: s.trace}}
			}
			body.Result = ir.Return{Value: ir.Pair{Left: s.state, Right: value}}
		}
	}
	return body
}

func (s *statefulLowerer) call(body *ir.Body, ins *ssa.Call) {
	args := ins.Call.Args
	switch {
	case subset.IsLength(ins):
		body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: s.length(s.value(args[0]))})
	case subset.IsSliceClone(ins):
		body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: s.value(args[0])})
	case ins.Call.Value == s.method.Callback:
		arg := s.value(args[0])
		policy := ir.Apply{Function: s.value(s.method.Callback), Argument: ir.ListLength{List: s.trace}}
		trace := s.fresh("trace", s.traceType)
		body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: ir.Apply{Function: policy, Argument: arg}},
			ir.Binding{Binder: trace, Value: ir.Cons{Head: arg, Tail: s.trace}})
		s.trace = ir.Ref(trace)
	default:
		target := ins.Call.StaticCallee()
		call := ir.Call{Callee: s.symbol(target), Args: []ir.Expr{s.state}}
		for _, arg := range args[1:] {
			call.Args = append(call.Args, s.value(arg))
		}
		stateType := ir.OptionType(s.record)
		result := s.fresh("transition", stateResult(target, stateType))
		state := s.fresh("state", stateType)
		body.Bindings = append(body.Bindings, ir.Binding{Binder: result, Value: call, CanPanic: true},
			ir.Binding{Binder: state, Value: ir.PairField{Value: ir.Ref(result)}})
		s.state = ir.Ref(state)
		if target.Signature.Results().Len() != 0 {
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: ir.PairField{Value: ir.Ref(result), Second: true}})
		}
	}
}
