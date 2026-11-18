//go:build golean_planned

package immutable_closure

//golean:verify
func AddOffset(value, offset int64) int64 {
	add := func(x int64) int64 { return x + offset }
	return add(value)
}
