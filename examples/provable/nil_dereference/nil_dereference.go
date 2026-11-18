//go:build golean_planned

package nil_dereference

type Record struct {
	Value int64
}

//golean:verify
func Read(record *Record) int64 { return record.Value }
