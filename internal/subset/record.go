package subset

import (
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

// RecordCell is a fresh allocation whose addresses stay local. An allocation
// with a dominating initializer can be lowered directly from its stored values.
// A mutable cell instead starts at its Go zero value and carries updates.
type RecordCell struct {
	Mutable bool
	Whole   *ssa.Store
	Fields  []*ssa.Store
}

func supportedFields(record *types.Struct, classify func(types.Type) ir.Type) bool {
	for field := range record.Fields() {
		// Pointer-containing records would need a separate recursive model.
		switch field.Type().Underlying().(type) {
		case *types.Pointer, *types.Map:
			return false
		case *types.Interface:
			if field.Name() == "_" || InterfaceHandle(field.Type()) == "" {
				return false
			}
			continue
		}
		if field.Name() == "_" || classify(field.Type()) == "" {
			return false
		}
	}
	return true
}

func interfaceRecord(t types.Type) bool {
	record, ok := t.Underlying().(*types.Struct)
	if !ok {
		return false
	}
	for field := range record.Fields() {
		if isInterfaceValue(field.Type()) || interfaceRecord(field.Type()) {
			return true
		}
	}
	return false
}

func (c *checker) checkRecord(fn *ssa.Function, pos token.Pos, t types.Type) error {
	record, ok := t.Underlying().(*types.Struct)
	if !ok {
		return nil
	}
	for field := range record.Fields() {
		if isInterfaceValue(field.Type()) {
			if !c.initializedFields[field] {
				return diagnostic(fn, pos, "interface field %s requires //golean:assume:initialized", field.Name())
			}
			if err := c.checkInterface(fn, pos, field.Type()); err != nil {
				return err
			}
		} else if err := c.checkRecord(fn, pos, field.Type()); err != nil {
			return err
		} else if c.initializedFields[field] {
			return diagnostic(fn, pos, "//golean:assume:initialized requires an interface field: %s", field.Name())
		}
	}
	return nil
}

func (c *checker) isRecordAddress(addr ssa.Value) bool {
	cell, ok := recordAddressBase(addr).(*ssa.Alloc)
	if !ok {
		return false
	}
	_, found := c.records[cell]
	return found
}

func IsReadOnlyRecordField(addr *ssa.FieldAddr) bool {
	return IsReadOnlyRecordPointer(recordAddressBase(addr))
}

func IsReadOnlyRecordPointer(value ssa.Value) bool {
	return Type(value.Type()).Pointee() != "" && supportedValue(value)
}

func recordAddressBase(addr ssa.Value) ssa.Value {
	for field, ok := addr.(*ssa.FieldAddr); ok; field, ok = addr.(*ssa.FieldAddr) {
		addr = field.X
	}
	return addr
}

func recordInitializer(cell *ssa.Alloc) (RecordCell, bool) {
	return recordInitializerWithInterfaces(cell, false)
}

func recordInitializerWithInterfaces(cell *ssa.Alloc, constructor bool) (RecordCell, bool) {
	named := cell.Type().Underlying().(*types.Pointer).Elem()
	record := named.Underlying().(*types.Struct)
	result := RecordCell{Fields: make([]*ssa.Store, record.NumFields())}
	var reads []ssa.Instruction
	for _, use := range *cell.Referrers() {
		switch use := use.(type) {
		case *ssa.Store:
			if use.Addr != cell || result.Whole != nil || !hasType(use.Val, Type(named)) {
				return RecordCell{}, false
			}
			result.Whole = use
		case *ssa.FieldAddr:
			fieldType := record.Field(use.Field).Type()
			for _, access := range *use.Referrers() {
				if store, ok := access.(*ssa.Store); ok {
					valid := hasType(store.Val, Type(fieldType))
					if constructor && isInterfaceValue(fieldType) {
						param, ok := store.Val.(*ssa.Parameter)
						valid = ok && types.Identical(param.Type(), fieldType)
					}
					if store.Addr != use || result.Fields[use.Field] != nil || !valid {
						return RecordCell{}, false
					}
					result.Fields[use.Field] = store
				} else if readsCell(access, use) {
					reads = append(reads, access)
				} else if nested, ok := access.(*ssa.FieldAddr); ok && nested.X == use {
					nestedReads, valid := projectionReads(nested)
					if !valid {
						return RecordCell{}, false
					}
					reads = append(reads, nestedReads...)
				} else {
					return RecordCell{}, false
				}
			}
		default:
			if !readsCell(use, cell) {
				return RecordCell{}, false
			}
			reads = append(reads, use)
		}
	}
	for index, store := range result.Fields {
		fieldType := record.Field(index).Type()
		if constructor && result.Whole == nil && store == nil &&
			!isInterfaceValue(fieldType) && !interfaceRecord(fieldType) {
			continue
		}
		if (store != nil) == (result.Whole != nil) {
			return RecordCell{}, false
		}
	}
	stores := result.Fields
	if result.Whole != nil {
		stores = []*ssa.Store{result.Whole}
	}
	for _, store := range stores {
		if store == nil {
			continue
		}
		for _, read := range reads {
			if !comesBefore(store, read) {
				return RecordCell{}, false
			}
		}
	}
	return result, true
}

// projectionReads admits a nested field address only for further projections or
// reads. Stores are restricted to whole values and top-level field initialization.
func projectionReads(addr *ssa.FieldAddr) ([]ssa.Instruction, bool) {
	var reads []ssa.Instruction
	for _, use := range *addr.Referrers() {
		if readsCell(use, addr) {
			reads = append(reads, use)
			continue
		}
		if index, ok := use.(*ssa.IndexAddr); ok && index.X == addr && arrayType(addr.Type()) != nil {
			for _, access := range *index.Referrers() {
				if !readsCell(access, index) {
					return nil, false
				}
			}
			continue
		}
		nested, ok := use.(*ssa.FieldAddr)
		if !ok || nested.X != addr {
			return nil, false
		}
		more, ok := projectionReads(nested)
		if !ok {
			return nil, false
		}
		reads = append(reads, more...)
	}
	return reads, true
}

// localRecordUses checks that a record address is used only for reads, stores,
// and further field projections within this function.
func localRecordUses(addr ssa.Value) bool {
	typ := Type(addr.Type().Underlying().(*types.Pointer).Elem())
	for _, use := range *addr.Referrers() {
		switch use := use.(type) {
		case *ssa.Store:
			if use.Addr != addr || !hasType(use.Val, typ) {
				return false
			}
		case *ssa.FieldAddr:
			if use.X != addr || !localRecordUses(use) {
				return false
			}
		case *ssa.IndexAddr:
			if elem, _ := typ.ArrayShape(); elem == "" || use.X != addr {
				return false
			}
		case *ssa.Slice:
			if !IsEmptySliceLiteral(use) {
				return false
			}
		default:
			if !readsCell(use, addr) {
				return false
			}
		}
	}
	return true
}
