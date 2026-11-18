// Package grid_game implements a grid game with an unreachable goal.
package grid_game

const Size = 8

type Position struct {
	X uint8
	Y uint8
}

type Direction uint8

const (
	Up Direction = iota
	Down
	Left
	Right
)

//golean:verify
func Start() Position {
	return Position{X: 1, Y: 1}
}

//golean:verify
func Won(position Position) bool {
	return position.X == 7 && position.Y == 1
}

func IsWall(position Position, wrap bool) bool {
	x, y := position.X, position.Y
	if x == 5 && y <= 1 {
		return true
	}
	if x >= 6 && y == 2 {
		return true
	}
	if !wrap {
		return false
	}
	if x == 0 && y <= 1 {
		return true
	}
	return x >= 6 && y == Size-1
}

func backward(coordinate uint8, wrap bool) uint8 {
	if coordinate > 0 {
		return coordinate - 1
	}
	if wrap {
		return Size - 1
	}
	return coordinate
}

func forward(coordinate uint8, wrap bool) uint8 {
	if coordinate < Size-1 {
		return coordinate + 1
	}
	if wrap {
		return 0
	}
	return coordinate
}

// Step applies one move to a position on the board.
//
//golean:verify
func Step(position Position, direction Direction, wrap bool) Position {
	var target Position
	switch direction {
	case Up:
		target = Position{X: position.X, Y: backward(position.Y, wrap)}
	case Down:
		target = Position{X: position.X, Y: forward(position.Y, wrap)}
	case Left:
		target = Position{X: backward(position.X, wrap), Y: position.Y}
	case Right:
		target = Position{X: forward(position.X, wrap), Y: position.Y}
	default:
		return position
	}
	if IsWall(target, wrap) {
		return position
	}
	return target
}
