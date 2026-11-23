// Package grid_game implements a grid game with an unreachable goal.
package grid_game

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

const Size = 8

type point struct {
	x uint8
	y uint8
}

const (
	Up uint8 = iota
	Down
	Left
	Right
)

//golean:export
func Start() point {
	return point{x: 1, y: 1}
}

//golean:verify youCantWin : ∀ (wrap : Bool) (moves : List UInt8),
//golean:verify+   Won (Replay moves wrap) = false
func Won(position point) bool {
	return position.x == 7 && position.y == 1
}

type cellKind uint8

const (
	Open cellKind = iota
	Wall
	WrapWall
)

// layout lists the rows from top to bottom and the cells from left to right.
func layout() lean.Array[lean.Array[cellKind]] {
	return lean.Array[lean.Array[cellKind]]{}.
		Push(lean.Array[cellKind]{}.Push(WrapWall).Push(Open).Push(Open).Push(Open).Push(Open).Push(Wall).Push(Open).Push(Open)).
		Push(lean.Array[cellKind]{}.Push(WrapWall).Push(Open).Push(Open).Push(Open).Push(Open).Push(Wall).Push(Open).Push(Open)).
		Push(lean.Array[cellKind]{}.Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Wall).Push(Wall)).
		Push(lean.Array[cellKind]{}.Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open)).
		Push(lean.Array[cellKind]{}.Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open)).
		Push(lean.Array[cellKind]{}.Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open)).
		Push(lean.Array[cellKind]{}.Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open)).
		Push(lean.Array[cellKind]{}.Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(Open).Push(WrapWall).Push(WrapWall))
}

func IsWall(position point, wrap bool) bool {
	row := layout().Get(cellIndex(position.y)).UnwrapOr(lean.Array[cellKind]{})
	cell := row.Get(cellIndex(position.x)).UnwrapOr(Open)
	return cell == Wall || (wrap && cell == WrapWall)
}

// cellIndex maps a byte coordinate to an array index in the modeled Go subset.
// Size is the first out-of-bounds index.
func cellIndex(coordinate uint8) uint {
	if coordinate == 0 {
		return 0
	}
	if coordinate == 1 {
		return 1
	}
	if coordinate == 2 {
		return 2
	}
	if coordinate == 3 {
		return 3
	}
	if coordinate == 4 {
		return 4
	}
	if coordinate == 5 {
		return 5
	}
	if coordinate == 6 {
		return 6
	}
	if coordinate == 7 {
		return 7
	}
	return Size
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
//golean:verify stepBoundedEdge : let actual := Step (point.mk 0 3) 2 false
//golean:verify+ let expected := (point.mk 0 3)
//golean:verify+ actual.«field:x» = expected.«field:x» ∧ actual.«field:y» = expected.«field:y»
//golean:verify stepLeftWraps : let actual := Step (point.mk 0 3) 2 true
//golean:verify+ let expected := (point.mk 7 3)
//golean:verify+ actual.«field:x» = expected.«field:x» ∧ actual.«field:y» = expected.«field:y»
//golean:verify stepRightWraps : let actual := Step (point.mk 7 3) 3 true
//golean:verify+ let expected := (point.mk 0 3)
//golean:verify+ actual.«field:x» = expected.«field:x» ∧ actual.«field:y» = expected.«field:y»
//golean:verify stepUpWraps : let actual := Step (point.mk 1 0) 0 true
//golean:verify+ let expected := (point.mk 1 7)
//golean:verify+ actual.«field:x» = expected.«field:x» ∧ actual.«field:y» = expected.«field:y»
//golean:verify stepDownWraps : let actual := Step (point.mk 1 7) 1 true
//golean:verify+ let expected := (point.mk 1 0)
//golean:verify+ actual.«field:x» = expected.«field:x» ∧ actual.«field:y» = expected.«field:y»
//golean:verify stepOrdinaryWall : let actual := Step (point.mk 4 1) 3 false
//golean:verify+ let expected := (point.mk 4 1)
//golean:verify+ actual.«field:x» = expected.«field:x» ∧ actual.«field:y» = expected.«field:y»
//golean:verify stepHorizontalSeamWall : let actual := (Step Start 2 true)
//golean:verify+ let expected := Start
//golean:verify+ actual.«field:x» = expected.«field:x» ∧ actual.«field:y» = expected.«field:y»
//golean:verify stepVerticalSeamWall : let actual := Step (point.mk 7 6) 1 true
//golean:verify+ let expected := (point.mk 7 6)
//golean:verify+ actual.«field:x» = expected.«field:x» ∧ actual.«field:y» = expected.«field:y»
//golean:verify stepUnknownDirection : let actual := (Step Start 255 true)
//golean:verify+ let expected := Start
//golean:verify+ actual.«field:x» = expected.«field:x» ∧ actual.«field:y» = expected.«field:y»
func Step(position point, direction uint8, wrap bool) point {
	if direction == Up {
		return moveIfOpen(position, point{x: position.x, y: backward(position.y, wrap)}, wrap)
	}
	if direction == Down {
		return moveIfOpen(position, point{x: position.x, y: forward(position.y, wrap)}, wrap)
	}
	if direction == Left {
		return moveIfOpen(position, point{x: backward(position.x, wrap), y: position.y}, wrap)
	}
	if direction == Right {
		return moveIfOpen(position, point{x: forward(position.x, wrap), y: position.y}, wrap)
	}
	return position
}

func moveIfOpen(position, target point, wrap bool) point {
	if IsWall(target, wrap) {
		return position
	}
	return target
}

type replayState struct {
	point point
	wrap  bool
}

func replayMove(move uint8, state replayState) replayState {
	return replayState{point: Step(state.point, move, state.wrap), wrap: state.wrap}
}

// Replay applies a finite history of moves from the start position.
//
//golean:export
func Replay(moves lean.List[uint8], wrap bool) point {
	return lean.FoldList(moves, replayState{point: Start(), wrap: wrap}, replayMove).point
}

func NewPosition(x, y uint8) point { return point{x: x, y: y} }
func (p point) X() uint8           { return p.x }
func (p point) Y() uint8           { return p.y }
