package lean

// FoldControl holds the next state and indicates whether traversal should stop.
type FoldControl[S any] struct {
	State S
	Stop  bool
}

// FoldN visits indices from zero up to n, excluding n.
func FoldN[S any](n uint, initial S, step func(uint, S) S) S {
	state := initial
	for i := uint(0); i < n; i++ {
		state = step(i, state)
	}
	return state
}

// FoldNUntil visits indices in order until step requests a stop or n is exhausted.
func FoldNUntil[S any](n uint, initial S, step func(uint, S) FoldControl[S]) FoldControl[S] {
	result := FoldControl[S]{State: initial}
	for i := uint(0); i < n; i++ {
		result = step(i, result.State)
		if result.Stop {
			return result
		}
	}
	return result
}

// FoldList visits elements from head to tail.
func FoldList[T, S any](list List[T], initial S, step func(T, S) S) S {
	state := initial
	for node := list.node; node != nil; node = node.tail.node {
		state = step(node.head, state)
	}
	return state
}

// FoldListUntil visits elements from head to tail until step requests a stop.
func FoldListUntil[T, S any](list List[T], initial S, step func(T, S) FoldControl[S]) FoldControl[S] {
	result := FoldControl[S]{State: initial}
	for node := list.node; node != nil; node = node.tail.node {
		result = step(node.head, result.State)
		if result.Stop {
			return result
		}
	}
	return result
}
