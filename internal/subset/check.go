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
	root      *ssa.Package
	functions []*ssa.Function
	records   map[*ssa.Alloc]RecordCell
	arrays    map[*ssa.Alloc]*ssa.Store
	loops     map[*ssa.Function]*CountedLoop
	ranges    map[*ssa.Function]*RangeFold
	builds    map[*ssa.Function]*SliceBuild
}

func (c Checked) Root() *ssa.Package         { return c.root }
func (c Checked) Functions() []*ssa.Function { return c.functions }

func (c Checked) CountedLoop(fn *ssa.Function) *CountedLoop { return c.loops[fn] }

func (c Checked) RangeFold(fn *ssa.Function) *RangeFold { return c.ranges[fn] }

func (c Checked) SliceBuild(fn *ssa.Function) *SliceBuild { return c.builds[fn] }

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
		visiting:  make(map[*ssa.Function]bool),
		done:      make(map[*ssa.Function]bool),
		cells:     make(map[*ssa.Alloc]*ssa.Store),
		records:   make(map[*ssa.Alloc]RecordCell),
		arrays:    make(map[*ssa.Alloc]*ssa.Store),
		loops:     make(map[*ssa.Function]*CountedLoop),
		ranges:    make(map[*ssa.Function]*RangeFold),
		builds:    make(map[*ssa.Function]*SliceBuild),
		freshMaps: make(map[*ssa.MakeMap]bool),
	}
	for _, fn := range program.Roots {
		if err := c.function(fn); err != nil {
			return Checked{}, err
		}
	}
	return Checked{
		root: program.Package, functions: c.ordered, records: c.records, arrays: c.arrays, loops: c.loops,
		ranges: c.ranges, builds: c.builds,
	}, nil
}

type checker struct {
	visiting  map[*ssa.Function]bool
	done      map[*ssa.Function]bool
	ordered   []*ssa.Function
	cells     map[*ssa.Alloc]*ssa.Store
	records   map[*ssa.Alloc]RecordCell
	arrays    map[*ssa.Alloc]*ssa.Store
	loops     map[*ssa.Function]*CountedLoop
	ranges    map[*ssa.Function]*RangeFold
	builds    map[*ssa.Function]*SliceBuild
	freshMaps map[*ssa.MakeMap]bool
}

func (c *checker) function(fn *ssa.Function) error {
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
	instance := len(fn.TypeArgs()) != 0
	if (!instance && (fn.Pkg == nil || fn.Synthetic != "")) || sig.Recv() != nil ||
		sig.Variadic() ||
		sig.Results().Len() != 1 || Type(sig.Results().At(0).Type()) == "" {
		return diagnostic(fn, fn.Pos(), "expected a top-level function with one supported result and no variadic arguments")
	}
	if Type(sig.Results().At(0).Type()).Pointee() != "" {
		return diagnostic(fn, fn.Pos(), "record pointers may not escape as results")
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
	if Type(sig.Results().At(0).Type()).SliceElem() != "" {
		if blocks, ok := matchLoopBlocks(fn); ok {
			build = checkSliceBuild(blocks)
		}
	}
	if instance && (build == nil || build.Callback == nil) {
		return diagnostic(fn, fn.Pos(), "calls to generic functions are unsupported outside validated callback slice construction")
	}
	for _, param := range fn.Params {
		if Type(param.Type()) == "" && !(instance && param == build.Callback) {
			return diagnostic(fn, param.Pos(), "parameter must have a supported scalar or record type")
		}
	}
	c.visiting[fn] = true
	if build != nil {
		c.builds[fn] = build
	} else if err := c.checkBody(fn); err != nil {
		return err
	}
	delete(c.visiting, fn)
	c.done[fn] = true
	c.ordered = append(c.ordered, fn)
	return nil
}

func (c *checker) checkBody(fn *ssa.Function) error {
	result := Type(fn.Signature.Results().At(0).Type())
	if key, _ := result.MapShape(); key != "" {
		fresh := freshMapResult(fn)
		if fresh == nil {
			return diagnostic(fn, fn.Pos(), "map results require a fresh local allocation with straight-line uses before return")
		}
		c.freshMaps[fresh] = true
	}
	if result.SliceElem() != "" {
		for _, block := range fn.Blocks {
			ret, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Return)
			if ok {
				// Calls are validated transitively and subject to this same rule.
				if call, ok := ret.Results[0].(*ssa.Call); !ok || call.Call.StaticCallee() == nil {
					return diagnostic(fn, fn.Pos(), "slice results require a validated fresh construction")
				}
			}
		}
	}
	if loop := checkCountedLoop(fn); loop != nil {
		c.loops[fn] = loop
		return nil
	}
	if fold := checkRangeFold(fn); fold != nil {
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
			if addr, ok := ins.X.(*ssa.IndexAddr); ok && c.isReadOnlyIndexAddr(addr) {
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
		if IsLength(ins) {
			if hasType(ins.Call.Args[0], ir.Bytes) {
				return nil
			}
			return diagnostic(fn, ins.Pos(), "len requires a supported Go string")
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
		if err := c.function(callee); err != nil {
			return diagnostic(fn, ins.Pos(), "call to %s: %w", callee, err)
		}
		build := c.builds[callee]
		for i, arg := range ins.Call.Args {
			if build != nil && callee.Params[i] == build.Callback {
				if err := c.checkCallback(fn, ins, arg); err != nil {
					return err
				}
				continue
			}
			if !supportedValue(arg) {
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
		if !c.isReadOnlyIndexAddr(ins) {
			return diagnostic(fn, ins.Pos(), "index address requires a supported sequence and integer index")
		}
		for _, use := range *ins.Referrers() {
			if !readsCell(use, ins) {
				return diagnostic(fn, use.Pos(), "element addresses may only be read")
			}
		}
		return nil
	case *ssa.Index:
		if elem, _ := Type(ins.X.Type()).ArrayShape(); elem != "" && supportedValue(ins.X) && supportedIndex(ins.Index) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "index requires a supported array value and integer index")
	case *ssa.Lookup:
		if ins.CommaOk && supportedMapLookup(ins) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "map lookup requires comma-ok on a supported integer map")
	case *ssa.Extract:
		if lookup, ok := ins.Tuple.(*ssa.Lookup); ok && lookup.CommaOk {
			if ins.Index == 0 || ins.Index == 1 {
				return nil
			}
		}
		return diagnostic(fn, ins.Pos(), "only comma-ok map lookup results may be extracted")
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
			return nil
		}
		return diagnostic(fn, ins.Pos(), "field selection requires a supported record value")
	case *ssa.If:
		if hasType(ins.Cond, ir.Bool) {
			return nil
		}
		return diagnostic(fn, ins.Cond.Pos(), "branch condition must be a supported bool value")
	case *ssa.Phi:
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
		if len(ins.Results) == 1 && supportedValue(ins.Results[0]) {
			return nil
		}
		return diagnostic(fn, ins.Pos(), "return must have one supported value")
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
	case *ssa.Const:
		if value.Value == nil {
			key, _ := typ.MapShape()
			return typ.Pointee() != "" || typ.SliceElem() != "" || key != ""
		}
		return typ.IsInteger() && value.Value.Kind() == constant.Int ||
			typ == ir.Bool && value.Value.Kind() == constant.Bool ||
			typ == ir.Bytes && value.Value.Kind() == constant.String ||
			(typ == ir.Float32 || typ == ir.Float64) &&
				(value.Value.Kind() == constant.Float || value.Value.Kind() == constant.Int)
	case *ssa.Parameter, *ssa.BinOp, *ssa.UnOp, *ssa.Call, *ssa.Phi, *ssa.Convert, *ssa.ChangeType, *ssa.Field, *ssa.Index, *ssa.Extract, *ssa.MakeMap:
		return true
	default:
		return false
	}
}

func Type(t types.Type) ir.Type {
	t = types.Unalias(t)
	if m, ok := t.(*types.Map); ok {
		return mapType(m)
	}
	if slice, ok := t.(*types.Slice); ok {
		if elem := sequenceElement(slice.Elem()); elem != "" {
			return ir.SliceType(elem)
		}
		return ""
	}
	if array, ok := t.(*types.Array); ok {
		if elem := sequenceElement(array.Elem()); elem != "" {
			return ir.ArrayType(elem, array.Len())
		}
		return ""
	}
	if pointer, ok := t.(*types.Pointer); ok {
		if pointee := Type(pointer.Elem()); pointee.IsRecord() {
			return ir.RecordPointer(pointee)
		}
		return ""
	}
	if param, ok := t.(*types.TypeParam); ok {
		return ir.TypeParameter(param.Index())
	}
	if named, ok := t.(*types.Named); ok {
		if fields, ok := named.Underlying().(*types.Struct); ok && supportedFields(fields) {
			if obj := named.Obj(); obj.Pkg() != nil && obj.Parent() == obj.Pkg().Scope() && named.TypeParams().Len() == 0 {
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

func sequenceElement(t types.Type) ir.Type {
	elem := Type(t)
	key, _ := elem.MapShape()
	if nested, _ := elem.ArrayShape(); nested != "" || elem.SliceElem() != "" || elem.Pointee() != "" || key != "" {
		return ""
	}
	return elem
}

func (c *checker) isReadOnlyIndexAddr(addr *ssa.IndexAddr) bool {
	cell, _ := addr.X.(*ssa.Alloc)
	return supportedIndex(addr.Index) &&
		(c.arrays[cell] != nil || Type(addr.X.Type()).SliceElem() != "" && supportedValue(addr.X))
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

var binary = map[token.Token]ir.Operator{
	token.ADD: ir.Add, token.SUB: ir.Subtract, token.MUL: ir.Multiply,
	token.QUO: ir.Divide,
	token.EQL: ir.Equal, token.NEQ: ir.NotEqual, token.LSS: ir.Less,
	token.LEQ: ir.LessEqual, token.GTR: ir.Greater, token.GEQ: ir.GreaterEqual,
}

func Binary(op token.Token) (ir.Operator, bool) {
	result, ok := binary[op]
	return result, ok
}
