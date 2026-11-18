package nil_dereference

type Record struct {
	Value int64
}

//golean:verify
func Read(record *Record) int64 { return record.Value }

//golean:verify
func Touch(record *Record) int64 {
	_ = &record.Value
	return 7
}
