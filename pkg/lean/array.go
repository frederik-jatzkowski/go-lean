package lean

import "slices"

// Array models Lean's Array. The zero value is empty.
type Array[T any] struct {
	items []T
}

// Push returns an array with value appended.
func (a Array[T]) Push(value T) Array[T] {
	items := make([]T, len(a.items)+1)
	copy(items, a.items)
	items[len(a.items)] = value
	return Array[T]{items: items}
}

// Pop drops the last element. An empty array stays empty.
func (a Array[T]) Pop() Array[T] {
	if len(a.items) == 0 {
		return a
	}
	return Array[T]{items: a.items[:len(a.items)-1]}
}

// Get returns the element at index, or None if index is out of bounds.
func (a Array[T]) Get(index uint) Option[T] {
	if index >= a.Size() {
		return None[T]()
	}
	return Some(a.items[index])
}

// Set replaces the element at index. An out-of-bounds index leaves a unchanged.
func (a Array[T]) Set(index uint, value T) Array[T] {
	if index >= a.Size() {
		return a
	}
	items := slices.Clone(a.items)
	items[index] = value
	return Array[T]{items: items}
}

// Size returns the number of elements.
func (a Array[T]) Size() uint {
	return uint(len(a.items))
}
