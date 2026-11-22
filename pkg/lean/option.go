package lean

// Option models Lean's Option. The zero value is None.
type Option[T any] struct {
	value   T
	present bool
}

// Some constructs an Option containing value.
func Some[T any](value T) Option[T] {
	return Option[T]{value: value, present: true}
}

// None constructs an Option with no value.
func None[T any]() Option[T] {
	return Option[T]{}
}

// IsSome reports whether the option contains a value.
func (o Option[T]) IsSome() bool {
	return o.present
}

// UnwrapOr returns the contained value or fallback if the option is empty.
func (o Option[T]) UnwrapOr(fallback T) T {
	if o.present {
		return o.value
	}
	return fallback
}
