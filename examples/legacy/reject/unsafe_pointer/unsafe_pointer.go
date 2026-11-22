//go:build golean_reject

package unsafe_pointer

import "unsafe"

//golean:export
func Address(value *int64) uintptr { return uintptr(unsafe.Pointer(value)) }
