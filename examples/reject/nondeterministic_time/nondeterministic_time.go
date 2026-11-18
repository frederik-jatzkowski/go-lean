//go:build golean_reject

package nondeterministic_time

import "time"

//golean:verify
func Timestamp() int64 { return time.Now().UnixNano() }
