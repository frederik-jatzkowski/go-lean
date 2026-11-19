//go:build golean_reject

package init_function

var ready bool

//golean:export
func init() { ready = true }
