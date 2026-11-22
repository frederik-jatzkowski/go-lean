package lean

// List models Lean's List as a persistent singly linked list.
// The zero value is empty.
type List[T any] struct {
	node *listNode[T]
}

type listNode[T any] struct {
	head T
	tail List[T]
}

// Nil constructs the empty list.
func Nil[T any]() List[T] {
	return List[T]{}
}

// Cons prepends head to tail in constant time.
func Cons[T any](head T, tail List[T]) List[T] {
	return List[T]{node: &listNode[T]{head: head, tail: tail}}
}

// IsEmpty reports whether the list is empty, like Lean's List.isEmpty.
func (l List[T]) IsEmpty() bool {
	return l.node == nil
}
