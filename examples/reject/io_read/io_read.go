//go:build golean_reject

package io_read

import "os"

//golean:export
func ReadByte() int64 {
	var buffer [1]byte
	if n, _ := os.Stdin.Read(buffer[:]); n == 0 {
		return -1
	}
	return int64(buffer[0])
}
