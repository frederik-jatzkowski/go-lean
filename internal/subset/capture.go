package subset

import (
	"go/token"
	"go/types"
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

// CaptureType represents the immutable value kept in a Go SSA capture cell.
func CaptureType(t types.Type) ir.Type {
	if pointer, ok := types.Unalias(t).(*types.Pointer); ok {
		typ := Type(pointer.Elem())
		key, _ := typ.MapShape()
		if elem, _ := typ.ArrayShape(); elem == "" && typ.Pointee() == "" && typ.SliceElem() == "" && key == "" {
			return typ
		}
	}
	return ""
}

func (c *checker) isCapture(value ssa.Value) bool {
	switch value := value.(type) {
	case *ssa.FreeVar:
		return true
	case *ssa.Alloc:
		return c.cells[value] != nil
	default:
		return false
	}
}

func isClosureCall(call *ssa.Call, fn *ssa.Function) bool {
	closure, ok := call.Call.Value.(*ssa.MakeClosure)
	return ok && closure.Fn == fn
}

func (c *checker) checkLocalMemory(fn *ssa.Function) error {
	for _, capture := range fn.FreeVars {
		if typ := CaptureType(capture.Type()); typ == "" || typ.IsRecord() {
			return diagnostic(fn, capture.Pos(), "closure capture must be a supported immutable value")
		}
		for _, use := range *capture.Referrers() {
			if !readsCell(use, capture) {
				return diagnostic(fn, use.Pos(), "closure captures may only be read")
			}
		}
	}
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			if c.collectionPackaging[ins] {
				continue
			}
			if cell, ok := ins.(*ssa.Alloc); ok {
				if typ := arrayValueType(cell); typ != "" {
					initial := arrayInitializer(cell, typ)
					if initial != nil && !arrayHasIndexedStore(cell) {
						c.arrays[cell] = initial
					} else {
						if !concreteArrayElement(arrayType(cell.Type())) {
							return diagnostic(fn, cell.Pos(), "mutable local arrays require concrete element types")
						}
						if !localRecordUses(cell) {
							return diagnostic(fn, cell.Pos(), "local array address must not escape")
						}
						c.records[cell] = RecordCell{Mutable: true}
					}
					continue
				}
				if CaptureType(cell.Type()).IsRecord() {
					recordType := cell.Type().Underlying().(*types.Pointer).Elem()
					if interfaceRecord(recordType) {
						if err := c.checkRecord(fn, cell.Pos(), recordType); err != nil {
							return err
						}
						constructor := c.directives[fn].Constructor && types.Identical(recordType, fn.Signature.Results().At(0).Type())
						record, ok := recordInitializerWithInterfaces(cell, constructor)
						if !ok || (record.Whole == nil) != constructor {
							if !constructor {
								return diagnostic(fn, cell.Pos(), "interface field records require a read-only local copy of an initialized value")
							}
							return diagnostic(fn, cell.Pos(), "constructor must initialize every interface field directly from a same-type parameter")
						}
						c.records[cell] = record
						continue
					}
					record, ok := recordInitializer(cell)
					if !ok {
						if !localRecordUses(cell) {
							return diagnostic(fn, cell.Pos(), "local record address must not escape")
						}
						record = RecordCell{Mutable: true}
					}
					c.records[cell] = record
					continue
				}
				initial := immutableInitializer(cell)
				if initial == nil {
					return diagnostic(fn, cell.Pos(), "unsupported local allocation or mutable capture")
				}
				c.cells[cell] = initial
			}
		}
	}
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			if c.collectionPackaging[ins] {
				continue
			}
			switch ins := ins.(type) {
			case *ssa.IndexAddr:
				for _, use := range *ins.Referrers() {
					if readsCell(use, ins) {
						continue
					}
					if store, ok := use.(*ssa.Store); ok && store.Addr == ins {
						continue // Checked at the store.
					}
					return diagnostic(fn, use.Pos(), "element addresses must stay local")
				}
			case *ssa.Store:
				if index, ok := ins.Addr.(*ssa.IndexAddr); ok {
					if c.owned[index.X] != nil && hasType(ins.Val, Type(index.X.Type()).SliceElem()) {
						continue
					}
					if c.isLocalArrayIndex(index) && hasType(ins.Val, Type(index.Type().Underlying().(*types.Pointer).Elem())) {
						continue
					}
					return diagnostic(fn, ins.Pos(), "indexed writes require a local array; slice elements are read-only")
				}
				if c.isRecordAddress(ins.Addr) {
					continue
				}
				cell, ok := ins.Addr.(*ssa.Alloc)
				if ok && c.arrays[cell] == ins {
					continue
				}
				if !ok || c.cells[cell] != ins {
					return diagnostic(fn, ins.Pos(), "unsupported store outside immutable capture initialization")
				}
			case *ssa.MakeClosure:
				if err := c.checkClosure(fn, ins); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

func readsCell(use ssa.Instruction, cell ssa.Value) bool {
	load, ok := use.(*ssa.UnOp)
	return ok && load.Op == token.MUL && load.X == cell
}

func immutableInitializer(cell *ssa.Alloc) *ssa.Store {
	typ := CaptureType(cell.Type())
	if typ == "" {
		return nil
	}
	var initial *ssa.Store
	captured := false
	for _, use := range *cell.Referrers() {
		switch use := use.(type) {
		case *ssa.Store:
			if initial != nil || use.Addr != cell || !hasType(use.Val, typ) {
				return nil
			}
			initial = use
		case *ssa.MakeClosure:
			captured = true
		default:
			if !readsCell(use, cell) {
				return nil
			}
		}
	}
	if initial == nil || !captured {
		return nil
	}
	for _, use := range *cell.Referrers() {
		if use != initial && !comesBefore(initial, use) {
			return nil
		}
	}
	return initial
}

func comesBefore(first, second ssa.Instruction) bool {
	block := first.Block()
	if block == second.Block() {
		return slices.Index(block.Instrs, first) < slices.Index(block.Instrs, second)
	}
	return block.Dominates(second.Block())
}

func (c *checker) checkClosure(fn *ssa.Function, closure *ssa.MakeClosure) error {
	callee, ok := closure.Fn.(*ssa.Function)
	if !ok || callee.Parent() != fn {
		return diagnostic(fn, closure.Pos(), "only locally created closures are supported")
	}
	for _, use := range *closure.Referrers() {
		call, ok := use.(*ssa.Call)
		if !ok || call.Call.Value != closure && !sliceCallbackUse(call, closure) {
			return diagnostic(fn, use.Pos(), "closures may only be used in direct calls or checked slice callbacks")
		}
	}
	for _, value := range closure.Bindings {
		cell, ok := value.(*ssa.Alloc)
		if !ok || c.cells[cell] == nil {
			return diagnostic(fn, closure.Pos(), "closure captures must be immutable local cells")
		}
	}
	return nil
}
