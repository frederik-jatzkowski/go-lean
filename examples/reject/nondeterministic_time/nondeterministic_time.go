//go:build golean_reject

package nondeterministic_time

import "time"

//golean:export
func Timestamp() int64 { return time.Now().UnixNano() }
