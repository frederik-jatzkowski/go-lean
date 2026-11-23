package grid_game

// Play shows the starting position and the position after each move.
// It stops when next returns false.
func Play(wrap bool, next func() (Direction, bool), show func(Position)) {
	position := Start()
	show(position)
	for {
		direction, ok := next()
		if !ok {
			return
		}
		position = Step(position, direction, wrap)
		show(position)
	}
}
