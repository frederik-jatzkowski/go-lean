// Package subset checks the reachable SSA that the Lean backend can represent.
package subset

import (
	"fmt"
	"go/constant"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

// Checked holds the validated functions in dependency-first order.
type Checked struct {
	contracts map[*types.TypeName][]string
	root      *ssa.Package
	functions []*ssa.Function
	records   map[*ssa.Alloc]RecordCell
	arrays    map[*ssa.Alloc]*ssa.Store
	loops     map[*ssa.Function]*CountedLoop
	ranges    map[*ssa.Function]*RangeFold
	builds    map[*ssa.Function]*SliceBuild
	chains    map[*ssa.Function]*ChainRecursion
	stateful  map[*ssa.Function]*StatefulMethod
}

func (c Checked) Root() *ssa.Package         { return c.root }
func (c Checked) Functions() []*ssa.Function { return c.functions }

func (c Checked) Stateful(fn *ssa.Function) *StatefulMethod { return c.stateful[fn] }

func (c Checked) CountedLoop(fn *ssa.Function) *CountedLoop { return c.loops[fn] }

func (c Checked) RangeFold(fn *ssa.Function) *RangeFold { return c.ranges[fn] }

func (c Checked) SliceBuild(fn *ssa.Function) *SliceBuild { return c.builds[fn] }

func (c Checked) ChainRecursion(fn *ssa.Function) *ChainRecursion { return c.chains[fn] }

func (c Checked) ArrayInitializer(value ssa.Value) *ssa.Store {
	cell, _ := value.(*ssa.Alloc)
	return c.arrays[cell]
}

func (c Checked) RecordCell(value ssa.Value) (RecordCell, bool) {
	if cell, ok := value.(*ssa.Alloc); ok {
		record, ok := c.records[cell]
		return record, ok
	}
	return RecordCell{}, false
}

func Check(program gosource.Program) (Checked, error) {
	c := checker{
		contracts: make(map[*types.TypeName][]string), interfaceDocs: program.InterfaceDocs,
		initializedFields: program.InitializedFields,
		directives:        program.Directives,
		visiting:          make(map[*ssa.Function]bool),
		done:              make(map[*ssa.Function]bool),
		cells:             make(map[*ssa.Alloc]*ssa.Store),
		records:           make(map[*ssa.Alloc]RecordCell),
		arrays:            make(map[*ssa.Alloc]*ssa.Store),
		loops:             make(map[*ssa.Function]*CountedLoop),
		ranges:            make(map[*ssa.Function]*RangeFold),
		builds:            make(map[*ssa.Function]*SliceBuild),
		chains:            make(map[*ssa.Function]*ChainRecursion),
		freshMaps:         make(map[*ssa.MakeMap]bool),
		stateful:          make(map[*ssa.Function]*StatefulMethod),
	}
	for _, fn := range program.Roots {
		if !program.Directives[fn].Constructor && writesReceiver(fn, make(map[*ssa.Function]bool)) {
			if err := c.checkStateful(fn); err != nil {
				return Checked{}, err
			}
			continue
		}
		if err := c.function(fn); err != nil {
			return Checked{}, err
		}
	}
	knownEffects := make(map[*ssa.Function]bool)
	for _, build := range c.builds {
		for _, callback := range build.Callbacks {
			build.Effectful = build.Effectful || callbackMayPanic(callback, knownEffects)
		}
	}
	return Checked{
		contracts: c.contracts, root: program.Package, functions: c.ordered, records: c.records, arrays: c.arrays, loops: c.loops,
		ranges: c.ranges, builds: c.builds, chains: c.chains, stateful: c.stateful,
	}, nil
}

type checker struct {
	initializedFields map[*types.Var]bool
	directives        map[*ssa.Function]gosource.Directives
	contracts         map[*types.TypeName][]string
	interfaceDocs     map[*types.TypeName]gosource.InterfaceDoc
	visiting          map[*ssa.Function]bool
	done              map[*ssa.Function]bool
	ordered           []*ssa.Function
	cells             map[*ssa.Alloc]*ssa.Store
	records           map[*ssa.Alloc]RecordCell
	arrays            map[*ssa.Alloc]*ssa.Store
	loops             map[*ssa.Function]*CountedLoop
	ranges            map[*ssa.Function]*RangeFold
	builds            map[*ssa.Function]*SliceBuild
	chains            map[*ssa.Function]*ChainRecursion
	freshMaps         map[*ssa.MakeMap]bool
	stateful          map[*ssa.Function]*StatefulMethod
}

func (c *checker) function(fn *ssa.Function) error {
	if c.stateful[fn] != nil {
		return diagnostic(fn, fn.Pos(), "stateful calls must use the tracked receiver")
	}
	if c.done[fn] {
		return nil
	}
	if c.visiting[fn] {
		return diagnostic(fn, fn.Pos(), "recursive calls are unsupported")
	}
	if len(fn.Blocks) == 0 {
		return diagnostic(fn, fn.Pos(), "Go body unavailable for %s", fn)
	}
	sig := fn.Signature
	constructor := c.directives[fn].Constructor
	if constructor && (sig.Recv() != nil || sig.Results().Len() != 1 ||
		sig.TypeParams().Len() != 0 || !interfaceRecord(sig.Results().At(0).Type())) {
		return diagnostic(fn, fn.Pos(), "//golean:verify:constructor requires a non-generic function returning one struct with initialized interface fields")
	}
	instance := len(fn.TypeArgs()) != 0
	if sig.RecvTypeParams().Len() != 0 ||
		(sig.Recv() != nil && fn.Synthetic != "") {
		return diagnostic(fn, fn.Pos(), "method must be a declared concrete method with a non-generic receiver")
	}
	if (!instance && (fn.Pkg == nil || fn.Synthetic != "")) ||
		sig.Variadic() || sig.Results().Len() == 0 {
		return diagnostic(fn, fn.Pos(), "expected a function or concrete method with supported results and no variadic arguments")
	}
	for entry := range sig.Results().Variables() {
		result := entry.Type()
		if isInterfaceValue(result) {
			if err := c.checkInterface(fn, fn.Pos(), result); err != nil {
				return err
			}
		} else if Type(result) == "" {
			return diagnostic(fn, fn.Pos(), "expected a function or concrete method with supported results and no variadic arguments")
		}
		if err := c.checkRecord(fn, fn.Pos(), result); err != nil {
			return err
		}
		if Type(result).Pointee() != "" {
			return diagnostic(fn, fn.Pos(), "record pointers may not escape as results")
		}
	}
	if parent := fn.Parent(); parent != nil && parent.TypeParams().Len() != 0 {
		return diagnostic(fn, fn.Pos(), "closures in generic functions are unsupported")
	}
	params := sig.TypeParams()
	var build *SliceBuild
	if instance {
		origin := fn.Origin()
		if origin == nil || origin.Pkg == nil || origin.Synthetic != "" {
			return diagnostic(fn, fn.Pos(), "generic instance requires a named Go definition")
		}
		params = origin.Signature.TypeParams()
	}
	for i := 0; i < params.Len(); i++ {
		param := params.At(i)
		if !unrestricted(param) {
			return diagnostic(fn, param.Obj().Pos(), "type parameter %s must use the unrestricted any constraint", param.Obj().Name())
		}
	}
	if hasSliceResult(sig.Results()) {
		build = checkSliceCopy(fn)
		if blocks, ok := matchLoopBlocks(fn); build == nil && ok {
			build = checkSliceBuild(blocks)
		}
		if build == nil {
			build = matchSliceIteration(fn)
		}
	}
	chain := checkChainRecursion(fn)
	for _, param := range fn.Params {
		if constructor && interfaceRecord(param.Type()) {
			return diagnostic(fn, param.Pos(), "constructor parameters may not contain interface fields")
		}
		if err := c.checkRecord(fn, param.Pos(), param.Type()); err != nil {
			return err
		}
		if InterfaceHandle(param.Type()) != "" {
			if err := c.checkInterface(fn, param.Pos(), param.Type()); err != nil {
				return err
			}
			continue
		}
		if Type(param.Type()) == "" && !(instance && build != nil && param == build.Callback) && !(chain != nil && param == chain.Input) {
			if _, linked := chainLink(param.Type()); linked {
				return diagnostic(fn, param.Pos(), "linked-list inputs require nil-guarded read-only recursion on the direct next field")
			}
			return diagnostic(fn, param.Pos(), "parameter must have a supported scalar or record type")
		}
	}
	c.visiting[fn] = true
	if build != nil {
		if build.Exit != nil {
			if err := c.checkResultOwnership(fn, build.Destination); err != nil {
				return err
			}
			for _, ins := range build.Exit.Instrs[build.ExitStart:] {
				if err := c.instruction(fn, ins); err != nil {
					return err
				}
			}
		}
		if build.Iteration != nil {
			if err := c.checkIteration(fn, build.Iteration); err != nil {
				return err
			}
		}
		c.builds[fn] = build
	} else if chain != nil {
		c.chains[fn] = chain
	} else if constructor {
		if err := c.checkOrdinaryBody(fn); err != nil {
			return err
		}
		if err := c.checkConstructor(fn); err != nil {
			return err
		}
	} else if err := c.checkBody(fn); err != nil {
		return err
	}
	delete(c.visiting, fn)
	c.done[fn] = true
	c.ordered = append(c.ordered, fn)
	return nil
}

func hasSliceResult(results *types.Tuple) bool {
	for result := range results.Variables() {
		if Type(result.Type()).SliceElem() != "" {
			return true
		}
	}
	return false
}

type callResultSlot struct {
	call  *ssa.Call
	index int
}

func staticResultSlot(value ssa.Value) (callResultSlot, bool) {
	var slot callResultSlot
	switch value := value.(type) {
	case *ssa.Call:
		slot.call = value
	case *ssa.Extract:
		slot.call, _ = value.Tuple.(*ssa.Call)
		slot.index = value.Index
	}
	return slot, slot.call != nil && slot.call.Call.StaticCallee() != nil
}

func (c *checker) checkResultOwnership(fn *ssa.Function, destination *ssa.MakeSlice) error {
	results := fn.Signature.Results()
	for index := 0; index < results.Len(); index++ {
		result := Type(results.At(index).Type())
		if key, _ := result.MapShape(); key != "" {
			fresh := freshMapResult(fn, index)
			if fresh != nil {
				c.freshMaps[fresh] = true
				continue
			}
			if results.Len() == 1 || !returnsStaticResult(fn, index, nil) {
				return diagnostic(fn, fn.Pos(), "map results require a fresh local allocation with local uses before return")
			}
		}
		if result.SliceElem() != "" && !returnsStaticResult(fn, index, destination) {
			return diagnostic(fn, fn.Pos(), "slice results require a validated fresh construction")
		}
	}
	for _, block := range fn.Blocks {
		if ret, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Return); ok {
			seen := make(map[callResultSlot]bool)
			for _, value := range ret.Results {
				typ := Type(value.Type())
				key, _ := typ.MapShape()
				if source, ok := staticResultSlot(value); ok && (typ.SliceElem() != "" || key != "") {
					if seen[source] {
						return diagnostic(fn, ret.Pos(), "aggregate results must have distinct fresh sources")
					}
					seen[source] = true
				}
			}
		}
	}
	return nil
}

// Static callees are validated transitively and subject to the same ownership rules.
func returnsStaticResult(fn *ssa.Function, index int, destination *ssa.MakeSlice) bool {
	for _, block := range fn.Blocks {
		ret, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Return)
		if !ok || destination != nil && ret.Results[index] == destination {
			continue
		}
		if _, ok := staticResultSlot(ret.Results[index]); !ok {
			return false
		}
	}
	return true
}

func (c *checker) checkBody(fn *ssa.Function) error {
	if err := c.checkResultOwnership(fn, nil); err != nil {
		return err
	}
	if loop := checkCountedLoop(fn); loop != nil {
		c.loops[fn] = loop
		return nil
	}
	if loop := matchStructuredCountedLoop(fn); loop != nil {
		if err := c.checkLoopState(fn, loop.Structured); err != nil {
			return err
		}
		c.loops[fn] = loop
		return nil
	}
	if fold := checkRangeFold(fn); fold != nil {
		c.ranges[fn] = fold
		return nil
	}
	if fold := matchStructuredFold(fn); fold != nil {
		if err := c.checkLoopState(fn, fold.Structured); err != nil {
			return err
		}
		c.ranges[fn] = fold
		return nil
	}
	return c.checkOrdinaryBody(fn)
}

func (c *checker) checkOrdinaryBody(fn *ssa.Function) error {
	if err := checkAcyclic(fn); err != nil {
		return err
	}
	if err := c.checkLocalMemory(fn); err != nil {
		return err
	}
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			if err := c.instruction(fn, ins); err != nil {
				return err
			}
		}
	}
	return nil
}

func checkAcyclic(fn *ssa.Function) error {
	const visiting, done = 1, 2
	states := make([]int, len(fn.Blocks))
	var visit func(*ssa.BasicBlock) error
	visit = func(block *ssa.BasicBlock) error {
		switch states[block.Index] {
		case visiting:
			return diagnostic(fn, block.Instrs[0].Pos(), "control-flow loops are unsupported")
		case done:
			return nil
		}
		states[block.Index] = visiting
		for _, successor := range block.Succs {
			if err := visit(successor); err != nil {
				return err
			}
		}
		states[block.Index] = done
		return nil
	}
	return visit(fn.Blocks[0])
}

func (c *checker) instruction(fn *ssa.Function, ins ssa.Instruction) error {
	switch ins := ins.(type) {
	case *ssa.BinOp:
		op, supported := Binary(ins.Op)
		typ := Type(ins.X.Type())
		if typ.SliceElem() != "" && (ins.Op == token.EQL || ins.Op == token.NEQ) &&
			(isNilSlice(ins.X) && supportedValue(ins.Y) || isNilSlice(ins.Y) && supportedValue(ins.X)) {
			return nil
		}
		if supported && supportedValue(ins.X) && hasType(ins.Y, typ) &&
			(typ.IsInteger() ||
				typ == ir.Bool && (ins.Op == token.EQL || ins.Op == token.NEQ) ||
				(typ == ir.Bytes || typ == ir.Float32) && ins.Op == token.ADD ||
				typ == ir.Float64 && op >= ir.Equal) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "unsupported runtime operation %s on %s and %s", ins.Op, ins.X.Type(), ins.Y.Type())
	case *ssa.UnOp:
		if ins.Op == token.MUL {
			cell, _ := ins.X.(*ssa.Alloc)
			if c.isCapture(ins.X) || c.isRecordAddress(ins.X) || c.arrays[cell] != nil || IsReadOnlyRecordPointer(ins.X) {
				return nil
			}
			if addr, ok := ins.X.(*ssa.FieldAddr); ok && IsReadOnlyRecordField(addr) {
				return nil
			}
			if addr, ok := ins.X.(*ssa.IndexAddr); ok && c.isSupportedIndexAddress(addr) {
				return nil
			}
		}
		if ins.Op == token.SUB && Type(ins.X.Type()).IsInteger() && supportedValue(ins.X) ||
			ins.Op == token.NOT && hasType(ins.X, ir.Bool) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "unsupported unary operation %s on %s", ins.Op, ins.X.Type())
	case *ssa.Convert:
		from, to := Type(ins.X.Type()), Type(ins.Type())
		if from.IsWord() && to.IsWord() && supportedValue(ins.X) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "unsupported conversion from %s to %s", ins.X.Type(), ins.Type())
	case *ssa.ChangeType:
		to := Type(ins.Type())
		if to.IsInteger() && hasType(ins.X, to) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "unsupported type change from %s to %s", ins.X.Type(), ins.Type())
	case *ssa.Call:
		if c.directives[fn].Constructor {
			return diagnostic(fn, ins.Pos(), "calls are unsupported in verified constructors")
		}
		if ins.Call.IsInvoke() {
			return c.checkInvoke(fn, ins)
		}
		if IsLength(ins) {
			arg := ins.Call.Args[0]
			if hasType(arg, ir.Bytes) || Type(arg.Type()).SliceElem() != "" && supportedValue(arg) {
				return nil
			}
			return diagnostic(fn, ins.Pos(), "len requires a supported Go string or slice")
		}
		callee := ins.Call.StaticCallee()
		if callee == nil {
			return diagnostic(fn, ins.Pos(), "unsupported call to %s; expected a statically resolved Go function", ins.Call.Value)
		}
		if parent := callee.Parent(); parent != nil &&
			(parent != fn || len(callee.FreeVars) != 0 && !isClosureCall(ins, callee)) {
			return diagnostic(fn, ins.Pos(), "closure call must use its original local closure")
		}
		if callee.Signature.TypeParams().Len() != 0 {
			return diagnostic(fn, ins.Pos(), "calls to generic functions are unsupported")
		}
		abstract := false
		for _, target := range c.directives[fn].Abstract {
			abstract = abstract || target.Callee == callee
		}
		if !abstract {
			if c.directives[callee].Constructor {
				return diagnostic(fn, ins.Pos(), "verified constructor calls are unsupported in checked functions")
			}
			if len(c.directives[callee].Abstract) != 0 {
				return diagnostic(fn, ins.Pos(), "calling an abstracted verification root in the same module is unsupported")
			}
			if err := c.function(callee); err != nil {
				return diagnostic(fn, ins.Pos(), "call to %s: %w", callee, err)
			}
		}
		build := c.builds[callee]
		for i, arg := range ins.Call.Args {
			if build != nil && callee.Params[i] == build.Callback {
				if err := c.checkCallback(fn, ins, arg, build); err != nil {
					return err
				}
				continue
			}
			if !supportedValue(arg) && !supportedHandle(arg) {
				return diagnostic(fn, ins.Pos(), "call to %s requires supported arguments", callee)
			}
		}
		return nil
	case *ssa.Alloc, *ssa.Store, *ssa.MakeClosure:
		// checkLocalMemory validates the lifetimes and uses of these instructions.
		return nil
	case *ssa.FieldAddr:
		if c.isRecordAddress(ins) {
			return nil
		}
		if IsReadOnlyRecordField(ins) {
			if _, valid := projectionReads(ins); valid {
				return nil
			}
			return diagnostic(fn, ins.Pos(), "field addresses from record inputs may only be projected or read")
		}
		return diagnostic(fn, ins.Pos(), "field address requires a supported record")
	case *ssa.IndexAddr:
		if !c.isSupportedIndexAddress(ins) {
			return diagnostic(fn, ins.Pos(), "index address requires a supported sequence and integer index")
		}
		return nil
	case *ssa.Index:
		if elem, _ := Type(ins.X.Type()).ArrayShape(); elem != "" && supportedValue(ins.X) && supportedIndex(ins.Index) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "index requires a supported array value and integer index")
	case *ssa.Slice:
		if IsEmptySliceLiteral(ins) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "reslicing is unsupported")
	case *ssa.Lookup:
		if supportedMapLookup(ins) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "map lookup requires a supported integer map")
	case *ssa.Extract:
		if lookup, ok := ins.Tuple.(*ssa.Lookup); ok && lookup.CommaOk {
			if ins.Index == 0 || ins.Index == 1 {
				return nil
			}
		}
		if call, ok := ins.Tuple.(*ssa.Call); ok && call.Call.StaticCallee() != nil &&
			ins.Index >= 0 && ins.Index < call.Call.Signature().Results().Len() &&
			call.Call.Signature().Results().Len() > 1 {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "only static call or comma-ok map lookup results may be extracted")
	case *ssa.MakeMap:
		if c.freshMaps[ins] {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "map allocation requires a validated fresh map result")
	case *ssa.MapUpdate:
		if fresh, ok := ins.Map.(*ssa.MakeMap); ok && c.freshMaps[fresh] {
			key, value := Type(fresh.Type()).MapShape()
			if hasType(ins.Key, key) && hasType(ins.Value, value) {
				return nil
			}
		}
		return diagnostic(fn, ins.Pos(), "map writes require a validated fresh map and supported key and value")
	case *ssa.Field:
		if Type(ins.X.Type()).IsRecord() && supportedValue(ins.X) {
			return c.checkRecord(fn, ins.Pos(), ins.X.Type())
		}
		return diagnostic(fn, ins.Pos(), "field selection requires a supported record value")
	case *ssa.If:
		if hasType(ins.Cond, ir.Bool) {
			return nil
		}
		return diagnostic(fn, ins.Cond.Pos(), "branch condition must be a supported bool value")
	case *ssa.MakeInterface, *ssa.ChangeInterface:
		return diagnostic(fn, ins.Pos(), "unsupported SSA instruction %T: interface conversions are unsupported", ins)
	case *ssa.TypeAssert:
		return diagnostic(fn, ins.Pos(), "type assertions are unsupported")
	case *ssa.Phi:
		if handle := InterfaceHandle(ins.Type()); handle != "" {
			for _, edge := range ins.Edges {
				if !supportedHandle(edge) || InterfaceHandle(edge.Type()) != handle {
					return diagnostic(fn, ins.Pos(), "interface joins require matching non-nil handles")
				}
			}
			return nil
		}
		typ := Type(ins.Type())
		if typ == "" {
			return diagnostic(fn, ins.Pos(), "control-flow joins require a supported value type")
		}
		for _, edge := range ins.Edges {
			if !hasType(edge, typ) {
				return diagnostic(fn, ins.Pos(), "control-flow joins require matching supported values")
			}
		}
		return nil
	case *ssa.Return:
		if c.directives[fn].Constructor {
			return c.checkConstructorReturn(fn, ins)
		}
		for _, value := range ins.Results {
			if !supportedValue(value) && !supportedHandle(value) {
				return diagnostic(fn, ins.Pos(), "return must have supported values")
			}
		}
		return nil
	case *ssa.Jump:
		return nil
	default:
		return diagnostic(fn, ins.Pos(), "unsupported SSA instruction %T", ins)
	}
}

func IsLength(call *ssa.Call) bool {
	builtin, ok := call.Call.Value.(*ssa.Builtin)
	return ok && builtin.Name() == "len"
}

func hasType(value ssa.Value, want ir.Type) bool {
	return Type(value.Type()) == want && supportedValue(value)
}

func supportedValue(value ssa.Value) bool {
	typ := Type(value.Type())
	if typ == "" {
		return false
	}
	switch value := value.(type) {
	case *ssa.Slice:
		return IsEmptySliceLiteral(value)
	case *ssa.Const:
		if value.Value == nil {
			key, _ := typ.MapShape()
			array, _ := typ.ArrayShape()
			return typ.Pointee() != "" || typ.SliceElem() != "" || key != "" ||
				array != "" && concreteArrayElement(arrayType(value.Type())) ||
				typ.IsRecord() && !interfaceRecord(value.Type())
		}
		return typ.IsInteger() && value.Value.Kind() == constant.Int ||
			typ == ir.Bool && value.Value.Kind() == constant.Bool ||
			typ == ir.Bytes && value.Value.Kind() == constant.String ||
			(typ == ir.Float32 || typ == ir.Float64) &&
				(value.Value.Kind() == constant.Float || value.Value.Kind() == constant.Int)
	case *ssa.Parameter, *ssa.BinOp, *ssa.UnOp, *ssa.Call, *ssa.Phi, *ssa.Convert, *ssa.ChangeType, *ssa.Field, *ssa.Index, *ssa.Extract, *ssa.Lookup, *ssa.MakeMap, *ssa.MakeSlice:
		return true
	default:
		return false
	}
}

func Type(t types.Type) ir.Type {
	return typeWithRecords(t, nil)
}

func typeWithRecords(t types.Type, active map[*types.Named]bool) ir.Type {
	t = types.Unalias(t)
	if m, ok := t.(*types.Map); ok {
		return mapType(m)
	}
	if slice, ok := t.(*types.Slice); ok {
		if elem := sequenceElement(slice.Elem(), active); elem != "" {
			return ir.SliceType(elem)
		}
		return ""
	}
	if array, ok := t.(*types.Array); ok {
		if elem := sequenceElement(array.Elem(), active); elem != "" {
			return ir.ArrayType(elem, array.Len())
		}
		return ""
	}
	if pointer, ok := t.(*types.Pointer); ok {
		if interfaceRecord(pointer.Elem()) {
			return ""
		}
		if pointee := typeWithRecords(pointer.Elem(), active); pointee.IsRecord() {
			return ir.RecordPointer(pointee)
		}
		return ""
	}
	if param, ok := t.(*types.TypeParam); ok {
		return ir.TypeParameter(param.Index())
	}
	if named, ok := t.(*types.Named); ok {
		if fields, ok := named.Underlying().(*types.Struct); ok {
			obj := named.Obj()
			if active[named] || obj.Pkg() == nil || obj.Parent() != obj.Pkg().Scope() || named.TypeParams().Len() != 0 {
				return ""
			}
			if active == nil {
				active = make(map[*types.Named]bool)
			}
			active[named] = true
			valid := supportedFields(fields, func(field types.Type) ir.Type { return typeWithRecords(field, active) })
			delete(active, named)
			if valid {
				return ir.RecordType(obj.Pkg().Path(), obj.Name())
			}
		}
		if basic, ok := named.Underlying().(*types.Basic); ok {
			if typ := Type(basic); typ.IsInteger() {
				return typ
			}
		}
		return ""
	}
	if basic, ok := t.(*types.Basic); ok {
		switch basic.Kind() {
		case types.Int:
			return ir.IntWord
		case types.Uint:
			return ir.UIntWord
		case types.Int8:
			return ir.Int8
		case types.Int16:
			return ir.Int16
		case types.Int32:
			return ir.Int32
		case types.Int64:
			return ir.Int64
		case types.Uint8:
			return ir.UInt8
		case types.Uint16:
			return ir.UInt16
		case types.Uint32:
			return ir.UInt32
		case types.Uint64:
			return ir.UInt64
		case types.Bool, types.UntypedBool:
			return ir.Bool
		case types.String, types.UntypedString:
			return ir.Bytes
		case types.Float32:
			return ir.Float32
		case types.Float64:
			return ir.Float64
		}
	}
	return ""
}

func sequenceElement(t types.Type, active map[*types.Named]bool) ir.Type {
	if interfaceRecord(t) {
		return ""
	}
	elem := typeWithRecords(t, active)
	key, _ := elem.MapShape()
	if nested, _ := elem.ArrayShape(); nested != "" || elem.SliceElem() != "" || elem.Pointee() != "" || key != "" {
		return ""
	}
	return elem
}

func (c *checker) isSupportedIndexAddress(addr *ssa.IndexAddr) bool {
	cell, _ := addr.X.(*ssa.Alloc)
	field, isField := addr.X.(*ssa.FieldAddr)
	return supportedIndex(addr.Index) &&
		(c.arrays[cell] != nil || c.isLocalArrayIndex(addr) ||
			isField && arrayType(addr.X.Type()) != nil && IsReadOnlyRecordField(field) ||
			Type(addr.X.Type()).SliceElem() != "" && supportedValue(addr.X))
}

func isNilSlice(value ssa.Value) bool {
	c, ok := value.(*ssa.Const)
	return ok && c.IsNil() && Type(value.Type()).SliceElem() != ""
}

func supportedIndex(index ssa.Value) bool {
	return Type(index.Type()).IsInteger() && supportedValue(index)
}

func unrestricted(param *types.TypeParam) bool {
	return types.Identical(param.Constraint(), types.Universe.Lookup("any").Type())
}

func diagnostic(fn *ssa.Function, pos token.Pos, format string, args ...any) error {
	if !pos.IsValid() {
		pos = fn.Pos()
	}
	return fmt.Errorf("%s: %w", fn.Prog.Fset.Position(pos), fmt.Errorf(format, args...))
}

//golean:verify
func Binary(op token.Token) (ir.Operator, bool) {
	switch op {
	case token.ADD:
		return ir.Add, true
	case token.SUB:
		return ir.Subtract, true
	case token.MUL:
		return ir.Multiply, true
	case token.QUO:
		return ir.Divide, true
	case token.REM:
		return ir.Remainder, true
	case token.EQL:
		return ir.Equal, true
	case token.NEQ:
		return ir.NotEqual, true
	case token.LSS:
		return ir.Less, true
	case token.LEQ:
		return ir.LessEqual, true
	case token.GTR:
		return ir.Greater, true
	case token.GEQ:
		return ir.GreaterEqual, true
	default:
		return 0, false
	}
}
