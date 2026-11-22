//go:build golean_reject

package escaping_alias

type Aliases struct {
	First  *int64
	Second *int64
}

//golean:export
func Duplicate(value *int64) Aliases { return Aliases{First: value, Second: value} }
