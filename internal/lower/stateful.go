package lower

import (
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

type statefulLowerer struct {
	*lowerer
	method     *sourceStateful
	record     ir.Type
	state      ir.Expr
	trace      ir.Expr
	traceType  ir.Type
	loop       ir.Symbol
	loopParams []ir.Expr
	fuel       ir.Expr
}

func (l *lowerer) statePayload(results []*sourceType) ir.Type {
	return productType(results, func(typ *sourceType) ir.Type {
		return stateType(l.valueType(typ))
	})
}

func stateType(typ ir.Type) ir.Type {
	if typ.SliceElem() == ir.Bytes {
		return ir.OptionType(ir.ProductType(typ, ir.Nat))
	}
	if typ.SliceElem() != "" {
		return ir.OptionType(typ)
	}
	return typ
}

func (l *lowerer) lowerStateful(fn *sourceFunction, method *sourceStateful) []ir.Function {
	named := method.Record
	recordType := ir.RecordType(named.Package, named.Name)
	record := ir.Record{Symbol: l.typeSymbol(named, "")}
	for _, field := range named.Fields {
		record.Fields = append(record.Fields, ir.Field{Name: field.Name, Type: stateType(l.valueType(field.Type))})
	}
	l.records[recordType] = record

	stateType := ir.OptionType(recordType)
	binder := l.bindAs(method.Receiver, stateType)
	s := statefulLowerer{lowerer: l, method: method, record: recordType, state: ir.Ref(binder)}
	result := ir.Function{Symbol: l.symbol(fn), CanPanic: true, Params: []ir.Binder{binder},
		Result: ir.ProductType(stateType, l.statePayload(fn.Results))}
	for _, param := range fn.Params[1:] {
		if param == method.Callback {
			input := l.valueType(method.CallbackInput)
			s.traceType = ir.SliceType(input)
			result.Result = ir.ProductType(stateType, ir.ProductType(l.statePayload(fn.Results), s.traceType))
			result.Params = append(result.Params, l.bindAs(param, ir.UnaryFunctionType(ir.Nat, ir.UnaryFunctionType(input, ir.Bool))))
		} else {
			result.Params = append(result.Params, s.bind(param))
		}
	}
	s.trace = ir.EmptySlice{}
	if method.Loop == nil {
		result.Body = s.body(fn.Entry, nil)
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
	result.Body = s.body(fn.Entry, nil)
	if s.traceType != "" {
		trace := s.fresh("trace", s.traceType)
		loop.Params = append(loop.Params, trace)
		s.trace = ir.Ref(trace)
	}
	s.state = ir.Ref(binder)
	s.fuel = ir.Ref(fuel)
	loop.Body = s.body(method.Loop.Header, fn.Entry)
	return []ir.Function{loop, result}
}

func (s *statefulLowerer) bind(value *sourceValue) ir.Binder {
	if value.Type.IsTuple {
		return s.bindAs(value, s.statePayload(value.Type.Tuple))
	}
	return s.bindAs(value, stateType(s.valueType(value.Type)))
}

func (s *statefulLowerer) fresh(name string, typ ir.Type) ir.Binder {
	return s.freshBinder(name, typ)
}

func (s *statefulLowerer) value(value *sourceValue) ir.Expr {
	if value.Kind == constantValue && value.IsNil && value.Type.Model.SliceElem() != "" {
		return ir.NilPointer{}
	}
	return s.lowerer.value(value)
}

func (s *statefulLowerer) project(addr *sourceValue) ir.Expr {
	return ir.CheckedRecordField{Value: s.state, Type: s.record, Name: addr.Field}
}

func (s *statefulLowerer) length(sequence ir.Expr) ir.Expr {
	s.usesWord = true
	return ir.SliceLength{List: ir.OptionGetD{Value: sequence, Default: ir.EmptySlice{}}}
}

func (s *statefulLowerer) child(block, predecessor *sourceBlock) ir.Body {
	if s.method.Loop != nil && block == s.method.Loop.Header {
		if s.fuel == nil {
			state := s.fresh("receiver", s.record)
			receiver := ir.Ref(state)
			sequence := ir.RecordField{Value: receiver, Name: s.method.Loop.Sequence.Field}
			cursor := ir.RecordField{Value: receiver, Name: s.method.Loop.Cursor.Field}
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
	child.lowerer = &lower
	result := child.body(block, predecessor)
	s.usesWord = s.usesWord || child.usesWord
	return result
}

func (s *statefulLowerer) body(block, predecessor *sourceBlock) ir.Body {
	var body ir.Body
	for _, ins := range block.Instructions {
		switch ins.Kind {
		case binaryValue:
			value := s.binary(ins)
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: value, CanPanic: value.Op.PanicsOnZeroDivisor()})
		case fieldAddress:
			if ins.X == s.method.Receiver {
				// Go checks the receiver at address formation, even for a later store.
				binder := s.fresh("receiver", s.record)
				body.Bindings = append(body.Bindings, ir.Binding{Binder: binder, Value: s.state, CanPanic: true})
			}
		case unaryValue:
			var value ir.Expr
			canPanic := false
			switch {
			case ins.Not:
				value = ir.Not{Value: s.value(ins.X)}
			case ins.Dereference:
				if field := ins.X; field.Kind == fieldAddress && field.X == s.method.Receiver {
					value, canPanic = s.project(field), true
				} else {
					value = s.load(ins.X)
				}
			default:
				value = ir.Negate{Value: s.value(ins.X)}
			}
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: value, CanPanic: canPanic})
		case indexAddress:
			typ := s.valueType(ins.X.Type)
			value := ir.CheckedIndex{Sequence: ir.OptionGetD{Value: s.value(ins.X), Default: ir.EmptySlice{}},
				SequenceType: typ, Index: s.value(ins.IndexValue), IndexType: s.valueType(ins.IndexValue.Type)}
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bindAs(ins, typ.SliceElem()), Value: value, CanPanic: true})
		case fieldValue:
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: ir.RecordField{Value: s.value(ins.X), Name: ins.Field}})
		case storeValue:
			if field := ins.X; field.Kind == fieldAddress && field.X == s.method.Receiver {
				receiver := s.fresh("receiver", s.record)
				state := s.fresh("state", ir.OptionType(s.record))
				update := ir.RecordUpdate{Record: ir.Ref(receiver), Field: field.Field, Value: s.value(ins.Value)}
				body.Bindings = append(body.Bindings, ir.Binding{Binder: receiver, Value: s.state, CanPanic: true},
					ir.Binding{Binder: state, Value: ir.Some{Value: update}})
				s.state = ir.Ref(state)
			}
		case callValue:
			s.call(&body, ins)
		case convertValue:
			binder := s.bind(ins)
			body.Bindings = append(body.Bindings, ir.Binding{Binder: binder, Value: ir.Convert{Value: s.value(ins.X), From: ins.X.Type.Model, To: binder.Type}})
		case changeType:
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: s.value(ins.X)})
		case phiValue:
			value := s.phiValue(ins, predecessor, s.value)
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: value})
		case ifValue:
			body.Result = ir.If{Condition: s.value(ins.X), Then: s.child(block.Succs[0], block), Else: s.child(block.Succs[1], block)}
		case jumpValue:
			next := s.child(block.Succs[0], block)
			body.Bindings = append(body.Bindings, next.Bindings...)
			body.Result = next.Result
		case extractValue:
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: s.lowerer.project(ins)})
		case returnValue:
			value := packResults(ins.Values, s.value)
			if s.traceType != "" {
				value = ir.Pair{Left: value, Right: ir.Reverse{List: s.trace}}
			}
			body.Result = ir.Return{Value: ir.Pair{Left: s.state, Right: value}}
		}
	}
	return body
}

func (s *statefulLowerer) call(body *ir.Body, ins *sourceValue) {
	args := ins.Call.Args
	switch {
	case ins.Call.Length:
		body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: s.length(s.value(args[0]))})
	case ins.Call.Clone:
		body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: s.value(args[0])})
	case ins.Call.Value == s.method.Callback:
		arg := s.value(args[0])
		policy := ir.Apply{Function: s.value(s.method.Callback), Argument: ir.ListLength{List: s.trace}}
		trace := s.fresh("trace", s.traceType)
		body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: ir.Apply{Function: policy, Argument: arg}},
			ir.Binding{Binder: trace, Value: ir.Cons{Head: arg, Tail: s.trace}})
		s.trace = ir.Ref(trace)
	default:
		target := ins.Call.Target
		call := ir.Call{Callee: s.symbol(target), Args: []ir.Expr{s.state}}
		for _, arg := range args[1:] {
			call.Args = append(call.Args, s.value(arg))
		}
		stateType := ir.OptionType(s.record)
		result := s.fresh("transition", ir.ProductType(stateType, s.statePayload(target.Results)))
		state := s.fresh("state", stateType)
		body.Bindings = append(body.Bindings, ir.Binding{Binder: result, Value: call, CanPanic: true},
			ir.Binding{Binder: state, Value: ir.PairField{Value: ir.Ref(result)}})
		s.state = ir.Ref(state)
		if len(target.Results) != 0 {
			body.Bindings = append(body.Bindings, ir.Binding{Binder: s.bind(ins), Value: ir.PairField{Value: ir.Ref(result), Second: true}})
		}
	}
}
