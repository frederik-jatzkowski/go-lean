package lean

import "slices"

// ByteArray models Lean's ByteArray. The zero value is empty.
type ByteArray struct {
	array Array[byte]
}

// ByteArrayFromBytes copies bytes into a ByteArray at a Go boundary.
func ByteArrayFromBytes(bytes []byte) ByteArray {
	return ByteArray{array: Array[byte]{items: slices.Clone(bytes)}}
}

// Get returns the byte at index, or None if index is out of bounds.
func (a ByteArray) Get(index uint) Option[byte] {
	return a.array.Get(index)
}

// Set replaces the byte at index. An out-of-bounds index leaves a unchanged.
func (a ByteArray) Set(index uint, value byte) ByteArray {
	return ByteArray{array: a.array.Set(index, value)}
}

// Push returns a byte array with value appended.
func (a ByteArray) Push(value byte) ByteArray {
	return ByteArray{array: a.array.Push(value)}
}

// Size returns the number of bytes.
func (a ByteArray) Size() uint {
	return a.array.Size()
}

// Extract returns bytes in [start, end), with end clamped to Size.
// The result is empty if start is at or beyond the clamped end.
func (a ByteArray) Extract(start, end uint) ByteArray {
	end = min(end, a.Size())
	if start >= end {
		return ByteArray{}
	}
	return ByteArray{array: Array[byte]{items: a.array.items[start:end]}}
}
