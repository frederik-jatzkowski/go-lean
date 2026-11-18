//go:build golean_reject

package unsafe_pointer

import "unsafe"

//golean:verify
func Address(value *int64) uintptr { return uintptr(unsafe.Pointer(value)) }
