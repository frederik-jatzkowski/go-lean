package nil_dereference

type Record struct {
	Value int64
}

//golean:verify readNonNilPanicFree : ∀ (record : Record),
//golean:verify+   ∃ value, Read (some record) = some value
//golean:verify readNilPanics : Read (none : Option Record) = none
//golean:verify readReturnsField : ∀ (record : Record),
//golean:verify+   Read (some record) = some record.«field:Value»
func Read(record *Record) int64 { return record.Value }

//golean:verify takingNilFieldAddressPanics : Touch (none : Option Record) = none
func Touch(record *Record) int64 {
	_ = &record.Value
	return 7
}
