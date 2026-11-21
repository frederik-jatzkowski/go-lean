package lower

import "github.com/frederik-jatzkowski/go-lean/internal/ir"

// These descriptors contain source facts only. They share identity within one
// read of Input. IR and the lowering environment are built separately.
type sourceProgram struct {
	Package   string
	Functions []*sourceFunction
}

// Existing list-only models need no slice identity. A module that observes
// nil or carries a slice in a record keeps that bit across its ordinary calls.
func usesNullableSlices(functions []*sourceFunction) bool {
	types := make(map[*sourceType]bool)
	var recordContainsSlice func(*sourceType) bool
	recordContainsSlice = func(typ *sourceType) bool {
		if typ == nil || types[typ] {
			return false
		}
		types[typ] = true
		for _, field := range typ.Fields {
			if field.Type.Model.SliceElem() != "" || recordContainsSlice(field.Type) {
				return true
			}
		}
		for _, element := range typ.Tuple {
			if recordContainsSlice(element) {
				return true
			}
		}
		return recordContainsSlice(typ.Elem)
	}
	for _, fn := range functions {
		if fn.Stateful != nil {
			continue
		}
		for _, param := range fn.Params {
			if recordContainsSlice(param.Type) {
				return true
			}
		}
		for _, result := range fn.Results {
			if recordContainsSlice(result) {
				return true
			}
		}
		visited := make(map[*sourceBlock]bool)
		var scan func(*sourceBlock) bool
		scan = func(block *sourceBlock) bool {
			if block == nil || visited[block] {
				return false
			}
			visited[block] = true
			for _, ins := range block.Instructions {
				if recordContainsSlice(ins.Type) || ins.Kind == binaryValue && ins.X.Type.Model.SliceElem() != "" {
					return true
				}
				for _, operand := range ins.Operands {
					if recordContainsSlice(operand.Value.Type) {
						return true
					}
				}
			}
			for _, next := range block.Succs {
				if scan(next) {
					return true
				}
			}
			return false
		}
		if scan(fn.Entry) {
			return true
		}
	}
	return false
}

type sourceFunction struct {
	ID                              int64
	Name, Package, Receiver, Origin string
	TypeParameters                  int
	Params, FreeVars                []*sourceValue
	Results                         []*sourceType
	Entry                           *sourceBlock
	Stateful                        *sourceStateful
	Counted                         *sourceCounted
	Range                           *sourceRange
	Build                           *sourceBuild
	Chain                           *sourceChain
}

type sourceBlock struct {
	ID           int64
	Instructions []*sourceValue
	Preds, Succs []*sourceBlock
}

type sourceType struct {
	Model                          ir.Type
	Name, Package                  string
	Elem                           *sourceType
	Tuple                          []*sourceType
	IsTuple, IsRecord, IsInterface bool
	Fields                         []*sourceField
	Methods                        []*sourceMethod
	Laws                           []string
}

type sourceField struct {
	Name string
	Type *sourceType
}

type sourceMethod struct {
	Name   string
	Params []*sourceType
	Result *sourceType
}

type valueKind int

const (
	otherValue valueKind = iota
	binaryValue
	unaryValue
	fieldValue
	fieldAddress
	indexAddress
	indexValue
	emptySliceValue
	stringSliceValue
	concreteErrorValue
	appendValue
	makeMap
	mapUpdate
	mapLookup
	extractValue
	callValue
	convertValue
	changeType
	allocValue
	storeValue
	ifValue
	phiValue
	returnValue
	jumpValue
	functionValue
	constantValue
	closureValue
	makeSlice
)

type sourceValue struct {
	CollectionRoot                                              *sourceValue
	ID                                                          int64
	Kind                                                        valueKind
	Name, Text, Field                                           string
	Type, FieldType, RecordType                                 *sourceType
	X, Y, Key, Value, IndexValue                                *sourceValue
	OperandIndex                                                int
	Values                                                      []*sourceValue
	Target                                                      *sourceFunction
	Op                                                          ir.Operator
	Not, Dereference, ReadOnly, CommaOK, IsNil, IsZero, Boolean bool
	Bits                                                        uint64
	Call                                                        *sourceCall
	Capture                                                     ir.Type
	ArrayInitial, RecordWhole                                   *sourceValue
	RecordFields                                                []*sourceValue
	HasCell, MutableCell, IndexInBounds                         bool
	Operands                                                    []*sourceOperand
}

type sourceOperand struct {
	Value     *sourceValue
	Dominates bool
}

type sourceCall struct {
	Args                    []*sourceValue
	Value                   *sourceValue
	Target                  *sourceFunction
	Method, Extremum        string
	Length, Clone, Capacity bool
}

type sourceStateful struct {
	Receiver, Callback    *sourceValue
	CallbackInput, Record *sourceType
	Loop                  *sourceIndexed
}
type sourceIndexed struct {
	Header           *sourceBlock
	Sequence, Cursor *sourceValue
}
type sourceCounted struct {
	Initial, State, Next, Start, Bound, Result *sourceValue
	Steps, Before, After                       []*sourceValue
	Structured                                 *sourceLoop
	Control, RangeGuard                        bool
}
type sourceRange struct {
	Initial, State, Next, Source, Element, Excluded, AppendTo *sourceValue
	Steps                                                     []*sourceValue
	Structured                                                *sourceLoop
	Prelude                                                   *sourceBlock
}
type sourceBuild struct {
	Destination, Copy, Source, Element, Value, Callback *sourceValue
	Exit                                                *sourceBlock
	ExitStart                                           int
	Lengths, Steps                                      []*sourceValue
	Effectful                                           bool
	CallbackType                                        ir.Type
	Iteration                                           *sourceIteration
}
type sourceChain struct {
	Input, Head, Tail   *sourceValue
	Element             ir.Type
	Base, Steps, Result []*sourceValue
}
type sourceLoop struct {
	Iteration       *sourceIteration
	Exit            *sourceBlock
	States, Initial []*sourceValue
	Next            []*sourceBackEdge
	Carried         []*sourceValue
}
type sourceBackEdge struct {
	Block  *sourceBlock
	Values []*sourceValue
}
type sourceIteration struct {
	Entry, Header *sourceBlock
	Skip          []*sourceValue
	Stores        []*sourceStore
}
type sourceStore struct {
	Instruction, Value *sourceValue
}

func capacitySliceTypes(functions []*sourceFunction) map[ir.Type]bool {
	result := make(map[ir.Type]bool)
	visited := make(map[*sourceBlock]bool)
	var scan func(*sourceBlock)
	scan = func(block *sourceBlock) {
		if block == nil || visited[block] {
			return
		}
		visited[block] = true
		for _, ins := range block.Instructions {
			if ins.Kind == callValue && ins.Call.Capacity {
				result[ins.Call.Args[0].Type.Model] = true
			}
		}
		for _, next := range block.Succs {
			scan(next)
		}
	}
	for _, fn := range functions {
		if fn.Range != nil && fn.Range.AppendTo != nil {
			result[fn.Range.AppendTo.Type.Model] = true
		}
		scan(fn.Entry)
	}
	return result
}
