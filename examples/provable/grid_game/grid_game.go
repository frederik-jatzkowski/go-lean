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

//golean:export
func Start() Position {
	return Position{X: 1, Y: 1}
}

//golean:verify youCantWin : ∀ (wrap : Bool) (moves : List UInt8),
//golean:verify+   Won (moves.foldl (fun position direction => Step position direction wrap) Start) = false
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
//golean:verify stepBoundedEdge : let actual := Step (Position.mk 0 3) 2 false
//golean:verify+ let expected := (Position.mk 0 3)
//golean:verify+ actual.«field:X» = expected.«field:X» ∧ actual.«field:Y» = expected.«field:Y»
//golean:verify stepLeftWraps : let actual := Step (Position.mk 0 3) 2 true
//golean:verify+ let expected := (Position.mk 7 3)
//golean:verify+ actual.«field:X» = expected.«field:X» ∧ actual.«field:Y» = expected.«field:Y»
//golean:verify stepRightWraps : let actual := Step (Position.mk 7 3) 3 true
//golean:verify+ let expected := (Position.mk 0 3)
//golean:verify+ actual.«field:X» = expected.«field:X» ∧ actual.«field:Y» = expected.«field:Y»
//golean:verify stepUpWraps : let actual := Step (Position.mk 1 0) 0 true
//golean:verify+ let expected := (Position.mk 1 7)
//golean:verify+ actual.«field:X» = expected.«field:X» ∧ actual.«field:Y» = expected.«field:Y»
//golean:verify stepDownWraps : let actual := Step (Position.mk 1 7) 1 true
//golean:verify+ let expected := (Position.mk 1 0)
//golean:verify+ actual.«field:X» = expected.«field:X» ∧ actual.«field:Y» = expected.«field:Y»
//golean:verify stepOrdinaryWall : let actual := Step (Position.mk 4 1) 3 false
//golean:verify+ let expected := (Position.mk 4 1)
//golean:verify+ actual.«field:X» = expected.«field:X» ∧ actual.«field:Y» = expected.«field:Y»
//golean:verify stepHorizontalSeamWall : let actual := (Step Start 2 true)
//golean:verify+ let expected := Start
//golean:verify+ actual.«field:X» = expected.«field:X» ∧ actual.«field:Y» = expected.«field:Y»
//golean:verify stepVerticalSeamWall : let actual := Step (Position.mk 7 6) 1 true
//golean:verify+ let expected := (Position.mk 7 6)
//golean:verify+ actual.«field:X» = expected.«field:X» ∧ actual.«field:Y» = expected.«field:Y»
//golean:verify stepUnknownDirection : let actual := (Step Start 255 true)
//golean:verify+ let expected := Start
//golean:verify+ actual.«field:X» = expected.«field:X» ∧ actual.«field:Y» = expected.«field:Y»
func Step(position Position, direction Direction, wrap bool) Position {
	if direction == Up {
		return moveIfOpen(position, Position{X: position.X, Y: backward(position.Y, wrap)}, wrap)
	}
	if direction == Down {
		return moveIfOpen(position, Position{X: position.X, Y: forward(position.Y, wrap)}, wrap)
	}
	if direction == Left {
		return moveIfOpen(position, Position{X: backward(position.X, wrap), Y: position.Y}, wrap)
	}
	if direction == Right {
		return moveIfOpen(position, Position{X: forward(position.X, wrap), Y: position.Y}, wrap)
	}
	return position
}

func moveIfOpen(position, target Position, wrap bool) Position {
	if IsWall(target, wrap) {
		return position
	}
	return target
}
