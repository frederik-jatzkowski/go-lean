package lower

import "github.com/frederik-jatzkowski/go-lean/internal/ir"

// These descriptors contain source facts only. They share identity within one
// read of Input. IR and the lowering environment are built separately.
type sourceProgram struct {
	Package   string
	Functions []*sourceFunction
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
)

type sourceValue struct {
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
	HasCell, MutableCell                                        bool
	Operands                                                    []*sourceOperand
}

type sourceOperand struct {
	Value     *sourceValue
	Dominates bool
}

type sourceCall struct {
	Args          []*sourceValue
	Value         *sourceValue
	Target        *sourceFunction
	Method        string
	Length, Clone bool
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
}
type sourceRange struct {
	Initial, State, Next, Source, Element *sourceValue
	Steps                                 []*sourceValue
	Structured                            *sourceLoop
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
