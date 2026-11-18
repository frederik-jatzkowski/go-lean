//go:build golean_reject

package reflection

import "reflect"

//golean:verify
func ReadAsInt(value int64) int64 { return reflect.ValueOf(value).Int() }
