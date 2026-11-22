package lower

type inputRow struct {
	numbers    map[int64]int64
	text       map[int64]string
	references map[int64][]int64
	strings    map[int64][]string
}

type inputGraph struct {
	phiBlocks        map[int64]int64
	functionOrders   map[int64]int64
	structuredLoops  map[int64]bool
	callOwners       map[int64]int64
	ordinaryOperands map[int64]bool
	ids              map[any]int64
	objects          []any
	rows             []*inputRow
}

type inputReader struct {
	input   Input
	objects map[int64]any
}

// sourceFields defines each source record's scalar layout once, for both the
// snapshot adapter and the core's reader. Selectors are local to a record kind.
type sourceFields struct {
	graph  *inputGraph
	row    *inputRow
	reader *inputReader
	id     int64
}

func encodeSource[T any](g *inputGraph, value *T, fields func(sourceFields, *T)) int64 {
	if value == nil {
		return 0
	}
	if id, ok := g.ids[value]; ok {
		return id
	}
	id := int64(len(g.rows)) + 1
	row := &inputRow{}
	g.ids[value] = id
	g.objects = append(g.objects, value)
	g.rows = append(g.rows, row)
	fields(sourceFields{graph: g, row: row, id: id}, value)
	return id
}

func decodeSource[T any](r *inputReader, id int64, fields func(sourceFields, *T)) *T {
	if id == 0 {
		return nil
	}
	if value, ok := r.objects[id]; ok {
		return value.(*T)
	}
	value := new(T)
	r.objects[id] = value
	fields(sourceFields{reader: r, id: id}, value)
	return value
}

func (g *inputGraph) encodeProgram(program *sourceProgram) {
	encodeSource(g, program, programFields)
}

func (r *inputReader) decodeFunction(id int64) *sourceFunction {
	return decodeSource(r, id, functionFields)
}

func (f sourceFields) setNumber(field, value int64) {
	if value != 0 {
		if f.row.numbers == nil {
			f.row.numbers = make(map[int64]int64)
		}
		f.row.numbers[field] = value
	}
}

func boolNumber(value bool) int64 {
	if value {
		return 1
	}
	return 0
}

func booleanField(f sourceFields, field int64, value *bool) {
	if f.reader == nil {
		f.setNumber(field, boolNumber(*value))
	} else {
		*value = f.reader.input.FieldNumber(f.id, field) != 0
	}
}

func numberField[T ~int | ~int64 | ~uint64](f sourceFields, field int64, value *T) {
	if f.reader == nil {
		f.setNumber(field, int64(*value))
	} else {
		*value = T(f.reader.input.FieldNumber(f.id, field))
	}
}

func textField[T ~string](f sourceFields, field int64, value *T) {
	if f.reader == nil {
		if *value != "" {
			if f.row.text == nil {
				f.row.text = make(map[int64]string)
			}
			f.row.text[field] = string(*value)
		}
	} else {
		*value = T(f.reader.input.FieldText(f.id, field))
	}
}

func textListField(f sourceFields, field int64, value *[]string) {
	if f.reader == nil {
		if len(*value) > 0 {
			if f.row.strings == nil {
				f.row.strings = make(map[int64][]string)
			}
			f.row.strings[field] = append([]string(nil), (*value)...)
		}
	} else if count := f.reader.input.TextCount(f.id, field); count > 0 {
		*value = make([]string, count)
		for i := range *value {
			(*value)[i] = f.reader.input.TextAt(f.id, field, int64(i))
		}
	}
}

func (f sourceFields) setReferences(field int64, ids []int64) {
	if f.row.references == nil {
		f.row.references = make(map[int64][]int64)
	}
	f.row.references[field] = ids
}

func referenceField[T any](f sourceFields, field int64, value **T, fields func(sourceFields, *T)) {
	if f.reader == nil {
		if id := encodeSource(f.graph, *value, fields); id != 0 {
			f.setReferences(field, []int64{id})
		}
	} else {
		*value = decodeSource(f.reader, f.reader.input.ReferenceAt(f.id, field, 0), fields)
	}
}

func referenceListField[T any](f sourceFields, field int64, values *[]*T, fields func(sourceFields, *T)) {
	if f.reader == nil {
		if len(*values) > 0 {
			ids := make([]int64, len(*values))
			for i, value := range *values {
				ids[i] = encodeSource(f.graph, value, fields)
			}
			f.setReferences(field, ids)
		}
	} else if count := f.reader.input.ReferenceCount(f.id, field); count > 0 {
		*values = make([]*T, count)
		for i := range *values {
			(*values)[i] = decodeSource(f.reader, f.reader.input.ReferenceAt(f.id, field, int64(i)), fields)
		}
	}
}

const (
	fieldProgramPackage int64 = iota
	fieldProgramFunctions
)

func programFields(f sourceFields, value *sourceProgram) {
	textField(f, fieldProgramPackage, &value.Package)
	referenceListField(f, fieldProgramFunctions, &value.Functions, functionFields)
}

const (
	fieldFunctionName int64 = iota
	fieldFunctionPackage
	fieldFunctionReceiver
	fieldFunctionOrigin
	fieldFunctionTypeParameters
	fieldFunctionParams
	fieldFunctionFreeVars
	fieldFunctionResults
	fieldFunctionEntry
	fieldFunctionStateful
	fieldFunctionCounted
	fieldFunctionRange
	fieldFunctionBuild
	fieldFunctionChain
	fieldFunctionDecreases
)

func functionFields(f sourceFields, value *sourceFunction) {
	if f.reader != nil {
		value.ID = f.id
	}
	textField(f, fieldFunctionName, &value.Name)
	textField(f, fieldFunctionPackage, &value.Package)
	textField(f, fieldFunctionReceiver, &value.Receiver)
	textField(f, fieldFunctionOrigin, &value.Origin)
	numberField(f, fieldFunctionTypeParameters, &value.TypeParameters)
	referenceListField(f, fieldFunctionParams, &value.Params, valueFields)
	referenceListField(f, fieldFunctionFreeVars, &value.FreeVars, valueFields)
	referenceListField(f, fieldFunctionResults, &value.Results, typeFields)
	referenceField(f, fieldFunctionEntry, &value.Entry, blockFields)
	referenceField(f, fieldFunctionStateful, &value.Stateful, statefulFields)
	referenceField(f, fieldFunctionCounted, &value.Counted, countedFields)
	referenceField(f, fieldFunctionRange, &value.Range, rangeFields)
	referenceField(f, fieldFunctionBuild, &value.Build, buildFields)
	referenceField(f, fieldFunctionChain, &value.Chain, chainFields)
	textField(f, fieldFunctionDecreases, &value.Decreases)
}

const (
	fieldBlockInstructions int64 = iota
	fieldBlockPreds
	fieldBlockSuccs
)

func blockFields(f sourceFields, value *sourceBlock) {
	if f.reader != nil {
		value.ID = f.id
	}
	referenceListField(f, fieldBlockInstructions, &value.Instructions, valueFields)
	referenceListField(f, fieldBlockPreds, &value.Preds, blockFields)
	referenceListField(f, fieldBlockSuccs, &value.Succs, blockFields)
}

const (
	fieldTypeModel int64 = iota
	fieldTypeName
	fieldTypePackage
	fieldTypeElem
	fieldTypeTuple
	fieldTypeIsTuple
	fieldTypeIsRecord
	fieldTypeFields
	fieldTypeMethods
	fieldTypeLaws
	fieldTypeIsInterface
)

func typeFields(f sourceFields, value *sourceType) {
	textField(f, fieldTypeModel, &value.Model)
	textField(f, fieldTypeName, &value.Name)
	textField(f, fieldTypePackage, &value.Package)
	referenceField(f, fieldTypeElem, &value.Elem, typeFields)
	referenceListField(f, fieldTypeTuple, &value.Tuple, typeFields)
	booleanField(f, fieldTypeIsTuple, &value.IsTuple)
	booleanField(f, fieldTypeIsRecord, &value.IsRecord)
	referenceListField(f, fieldTypeFields, &value.Fields, fieldFields)
	referenceListField(f, fieldTypeMethods, &value.Methods, methodFields)
	textListField(f, fieldTypeLaws, &value.Laws)
	booleanField(f, fieldTypeIsInterface, &value.IsInterface)
}

const (
	fieldFieldName int64 = iota
	fieldFieldType
)

func fieldFields(f sourceFields, value *sourceField) {
	textField(f, fieldFieldName, &value.Name)
	referenceField(f, fieldFieldType, &value.Type, typeFields)
}

const (
	fieldMethodName int64 = iota
	fieldMethodParams
	fieldMethodResult
)

func methodFields(f sourceFields, value *sourceMethod) {
	textField(f, fieldMethodName, &value.Name)
	referenceListField(f, fieldMethodParams, &value.Params, typeFields)
	referenceField(f, fieldMethodResult, &value.Result, typeFields)
}

const (
	fieldValueKind int64 = iota
	fieldValueName
	fieldValueText
	fieldValueField
	fieldValueType
	fieldValueFieldType
	fieldValueRecordType
	fieldValueX
	fieldValueY
	fieldValueKey
	fieldValueValue
	fieldValueIndexValue
	fieldValueOperandIndex
	fieldValueValues
	fieldValueTarget
	fieldValueOp
	fieldValueNot
	fieldValueDereference
	fieldValueReadOnly
	fieldValueCommaOK
	fieldValueIsNil
	fieldValueIsZero
	fieldValueBoolean
	fieldValueBits
	fieldValueCall
	fieldValueCapture
	fieldValueArrayInitial
	fieldValueRecordWhole
	fieldValueRecordFields
	fieldValueHasCell
	fieldValueMutableCell
	fieldValueOperands
	fieldValueCollectionRoot
	fieldValueIndexInBounds
)

func valueFields(f sourceFields, value *sourceValue) {
	if f.reader != nil {
		value.ID = f.id
	}
	numberField(f, fieldValueKind, &value.Kind)
	textField(f, fieldValueName, &value.Name)
	textField(f, fieldValueText, &value.Text)
	textField(f, fieldValueField, &value.Field)
	referenceField(f, fieldValueType, &value.Type, typeFields)
	referenceField(f, fieldValueFieldType, &value.FieldType, typeFields)
	referenceField(f, fieldValueRecordType, &value.RecordType, typeFields)
	referenceField(f, fieldValueX, &value.X, valueFields)
	referenceField(f, fieldValueY, &value.Y, valueFields)
	referenceField(f, fieldValueKey, &value.Key, valueFields)
	referenceField(f, fieldValueValue, &value.Value, valueFields)
	referenceField(f, fieldValueIndexValue, &value.IndexValue, valueFields)
	numberField(f, fieldValueOperandIndex, &value.OperandIndex)
	referenceListField(f, fieldValueValues, &value.Values, valueFields)
	referenceField(f, fieldValueTarget, &value.Target, functionFields)
	numberField(f, fieldValueOp, &value.Op)
	booleanField(f, fieldValueNot, &value.Not)
	booleanField(f, fieldValueDereference, &value.Dereference)
	booleanField(f, fieldValueReadOnly, &value.ReadOnly)
	booleanField(f, fieldValueCommaOK, &value.CommaOK)
	booleanField(f, fieldValueIsNil, &value.IsNil)
	booleanField(f, fieldValueIsZero, &value.IsZero)
	booleanField(f, fieldValueBoolean, &value.Boolean)
	numberField(f, fieldValueBits, &value.Bits)
	referenceField(f, fieldValueCall, &value.Call, callFields)
	textField(f, fieldValueCapture, &value.Capture)
	referenceField(f, fieldValueArrayInitial, &value.ArrayInitial, valueFields)
	referenceField(f, fieldValueRecordWhole, &value.RecordWhole, valueFields)
	referenceListField(f, fieldValueRecordFields, &value.RecordFields, valueFields)
	booleanField(f, fieldValueHasCell, &value.HasCell)
	booleanField(f, fieldValueMutableCell, &value.MutableCell)
	referenceListField(f, fieldValueOperands, &value.Operands, operandFields)
	referenceField(f, fieldValueCollectionRoot, &value.CollectionRoot, valueFields)
	booleanField(f, fieldValueIndexInBounds, &value.IndexInBounds)
}

const (
	fieldOperandValue int64 = iota
	fieldOperandDominates
)

func operandFields(f sourceFields, value *sourceOperand) {
	referenceField(f, fieldOperandValue, &value.Value, valueFields)
	booleanField(f, fieldOperandDominates, &value.Dominates)
}

const (
	fieldCallArgs int64 = iota
	fieldCallValue
	fieldCallTarget
	fieldCallMethod
	fieldCallLength
	fieldCallClone
	fieldCallExtremum
	fieldCallCapacity
	fieldCallRecursiveSite
)

func callFields(f sourceFields, value *sourceCall) {
	referenceListField(f, fieldCallArgs, &value.Args, valueFields)
	referenceField(f, fieldCallValue, &value.Value, valueFields)
	referenceField(f, fieldCallTarget, &value.Target, functionFields)
	textField(f, fieldCallMethod, &value.Method)
	booleanField(f, fieldCallLength, &value.Length)
	booleanField(f, fieldCallClone, &value.Clone)
	textField(f, fieldCallExtremum, &value.Extremum)
	booleanField(f, fieldCallCapacity, &value.Capacity)
	textField(f, fieldCallRecursiveSite, &value.RecursiveSite)
}

const (
	fieldStatefulReceiver int64 = iota
	fieldStatefulCallback
	fieldStatefulCallbackInput
	fieldStatefulRecord
	fieldStatefulLoop
	fieldStatefulBuffers
)

func statefulFields(f sourceFields, value *sourceStateful) {
	referenceField(f, fieldStatefulReceiver, &value.Receiver, valueFields)
	referenceField(f, fieldStatefulCallback, &value.Callback, valueFields)
	referenceField(f, fieldStatefulCallbackInput, &value.CallbackInput, typeFields)
	referenceField(f, fieldStatefulRecord, &value.Record, typeFields)
	referenceField(f, fieldStatefulLoop, &value.Loop, indexedFields)
	textListField(f, fieldStatefulBuffers, &value.Buffers)
}

const (
	fieldIndexedHeader int64 = iota
	fieldIndexedSequence
	fieldIndexedCursor
)

func indexedFields(f sourceFields, value *sourceIndexed) {
	referenceField(f, fieldIndexedHeader, &value.Header, blockFields)
	referenceField(f, fieldIndexedSequence, &value.Sequence, valueFields)
	referenceField(f, fieldIndexedCursor, &value.Cursor, valueFields)
}

const (
	fieldCountedInitial int64 = iota
	fieldCountedState
	fieldCountedNext
	fieldCountedStart
	fieldCountedBound
	fieldCountedResult
	fieldCountedSteps
	fieldCountedBefore
	fieldCountedAfter
	fieldCountedStructured
	fieldCountedControl
	fieldCountedRangeGuard
)

func countedFields(f sourceFields, value *sourceCounted) {
	referenceField(f, fieldCountedInitial, &value.Initial, valueFields)
	referenceField(f, fieldCountedState, &value.State, valueFields)
	referenceField(f, fieldCountedNext, &value.Next, valueFields)
	referenceField(f, fieldCountedStart, &value.Start, valueFields)
	referenceField(f, fieldCountedBound, &value.Bound, valueFields)
	referenceField(f, fieldCountedResult, &value.Result, valueFields)
	referenceListField(f, fieldCountedSteps, &value.Steps, valueFields)
	referenceListField(f, fieldCountedBefore, &value.Before, valueFields)
	referenceListField(f, fieldCountedAfter, &value.After, valueFields)
	referenceField(f, fieldCountedStructured, &value.Structured, loopFields)
	booleanField(f, fieldCountedControl, &value.Control)
	booleanField(f, fieldCountedRangeGuard, &value.RangeGuard)
}

const (
	fieldRangeInitial int64 = iota
	fieldRangeState
	fieldRangeNext
	fieldRangeSource
	fieldRangeElement
	fieldRangeSteps
	fieldRangeStructured
	fieldRangeExcluded
	fieldRangeAppendTo
	fieldRangePrelude
)

func rangeFields(f sourceFields, value *sourceRange) {
	referenceField(f, fieldRangeInitial, &value.Initial, valueFields)
	referenceField(f, fieldRangeState, &value.State, valueFields)
	referenceField(f, fieldRangeNext, &value.Next, valueFields)
	referenceField(f, fieldRangeSource, &value.Source, valueFields)
	referenceField(f, fieldRangeElement, &value.Element, valueFields)
	referenceListField(f, fieldRangeSteps, &value.Steps, valueFields)
	referenceField(f, fieldRangeStructured, &value.Structured, loopFields)
	referenceField(f, fieldRangeExcluded, &value.Excluded, valueFields)
	referenceField(f, fieldRangeAppendTo, &value.AppendTo, valueFields)
	referenceField(f, fieldRangePrelude, &value.Prelude, blockFields)
}

const (
	fieldBuildDestination int64 = iota
	fieldBuildCopy
	fieldBuildSource
	fieldBuildElement
	fieldBuildValue
	fieldBuildCallback
	fieldBuildExit
	fieldBuildExitStart
	fieldBuildLengths
	fieldBuildSteps
	fieldBuildEffectful
	fieldBuildCallbackType
	fieldBuildIteration
)

func buildFields(f sourceFields, value *sourceBuild) {
	referenceField(f, fieldBuildDestination, &value.Destination, valueFields)
	referenceField(f, fieldBuildCopy, &value.Copy, valueFields)
	referenceField(f, fieldBuildSource, &value.Source, valueFields)
	referenceField(f, fieldBuildElement, &value.Element, valueFields)
	referenceField(f, fieldBuildValue, &value.Value, valueFields)
	referenceField(f, fieldBuildCallback, &value.Callback, valueFields)
	referenceField(f, fieldBuildExit, &value.Exit, blockFields)
	numberField(f, fieldBuildExitStart, &value.ExitStart)
	referenceListField(f, fieldBuildLengths, &value.Lengths, valueFields)
	referenceListField(f, fieldBuildSteps, &value.Steps, valueFields)
	booleanField(f, fieldBuildEffectful, &value.Effectful)
	textField(f, fieldBuildCallbackType, &value.CallbackType)
	referenceField(f, fieldBuildIteration, &value.Iteration, iterationFields)
}

const (
	fieldChainInput int64 = iota
	fieldChainHead
	fieldChainTail
	fieldChainElement
	fieldChainBase
	fieldChainSteps
	fieldChainResult
)

func chainFields(f sourceFields, value *sourceChain) {
	referenceField(f, fieldChainInput, &value.Input, valueFields)
	referenceField(f, fieldChainHead, &value.Head, valueFields)
	referenceField(f, fieldChainTail, &value.Tail, valueFields)
	textField(f, fieldChainElement, &value.Element)
	referenceListField(f, fieldChainBase, &value.Base, valueFields)
	referenceListField(f, fieldChainSteps, &value.Steps, valueFields)
	referenceListField(f, fieldChainResult, &value.Result, valueFields)
}

const (
	fieldLoopIteration int64 = iota
	fieldLoopExit
	fieldLoopStates
	fieldLoopInitial
	fieldLoopNext
	fieldLoopCarried
)

func loopFields(f sourceFields, value *sourceLoop) {
	referenceField(f, fieldLoopIteration, &value.Iteration, iterationFields)
	referenceField(f, fieldLoopExit, &value.Exit, blockFields)
	referenceListField(f, fieldLoopStates, &value.States, valueFields)
	referenceListField(f, fieldLoopInitial, &value.Initial, valueFields)
	referenceListField(f, fieldLoopNext, &value.Next, backEdgeFields)
	referenceListField(f, fieldLoopCarried, &value.Carried, valueFields)
}

const (
	fieldBackEdgeBlock int64 = iota
	fieldBackEdgeValues
)

func backEdgeFields(f sourceFields, value *sourceBackEdge) {
	referenceField(f, fieldBackEdgeBlock, &value.Block, blockFields)
	referenceListField(f, fieldBackEdgeValues, &value.Values, valueFields)
}

const (
	fieldIterationEntry int64 = iota
	fieldIterationHeader
	fieldIterationSkip
	fieldIterationStores
)

func iterationFields(f sourceFields, value *sourceIteration) {
	referenceField(f, fieldIterationEntry, &value.Entry, blockFields)
	referenceField(f, fieldIterationHeader, &value.Header, blockFields)
	referenceListField(f, fieldIterationSkip, &value.Skip, valueFields)
	referenceListField(f, fieldIterationStores, &value.Stores, storeFields)
}

const (
	fieldStoreInstruction int64 = iota
	fieldStoreValue
)

func storeFields(f sourceFields, value *sourceStore) {
	referenceField(f, fieldStoreInstruction, &value.Instruction, valueFields)
	referenceField(f, fieldStoreValue, &value.Value, valueFields)
}
