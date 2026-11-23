package lean

// Box stores a value behind private indirection. Its zero value is empty.
type Box[T any] struct {
	value *T
}

// NewBox stores a copy of value.
func NewBox[T any](value T) Box[T] {
	return Box[T]{value: &value}
}

// IsSome reports whether the box contains a value.
func (b Box[T]) IsSome() bool {
	return b.value != nil
}

// Get returns a copy of the payload or the zero value of T.
func (b Box[T]) Get() T {
	if b.value != nil {
		return *b.value
	}
	var zero T
	return zero
}
