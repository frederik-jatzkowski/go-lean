package subset

import (
	"go/types"

	"golang.org/x/tools/go/ssa"
)

// RecordCell is a fresh allocation initialized by a whole-record store or by one
// store per field. Initializers dominate all reads, and addresses stay local.
type RecordCell struct {
	Whole  *ssa.Store
	Fields []*ssa.Store
}

func supportedFields(record *types.Struct) bool {
	for field := range record.Fields() {
		if field.Embedded() || field.Name() == "_" {
			return false
		}
		if _, basic := field.Type().Underlying().(*types.Basic); !basic || Type(field.Type()) == "" {
			return false
		}
	}
	return true
}

func (c *checker) isRecordAddress(addr ssa.Value) bool {
	if field, ok := addr.(*ssa.FieldAddr); ok {
		addr = field.X
	}
	cell, ok := addr.(*ssa.Alloc)
	if !ok {
		return false
	}
	_, found := c.records[cell]
	return found
}

func recordInitializer(cell *ssa.Alloc) (RecordCell, bool) {
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
			typ := Type(record.Field(use.Field).Type())
			for _, access := range *use.Referrers() {
				if store, ok := access.(*ssa.Store); ok {
					if store.Addr != use || result.Fields[use.Field] != nil || !hasType(store.Val, typ) {
						return RecordCell{}, false
					}
					result.Fields[use.Field] = store
				} else if readsCell(access, use) {
					reads = append(reads, access)
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
	for _, store := range result.Fields {
		if (store != nil) == (result.Whole != nil) {
			return RecordCell{}, false
		}
	}
	stores := result.Fields
	if result.Whole != nil {
		stores = []*ssa.Store{result.Whole}
	}
	for _, store := range stores {
		for _, read := range reads {
			if !comesBefore(store, read) {
				return RecordCell{}, false
			}
		}
	}
	return result, true
}
