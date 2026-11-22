// Package morris implements the rules of a two-player Nine Men's Morris game.
package morris

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type Result uint8

const (
	Ongoing Result = iota
	WhiteWins
	BlackWins
	Draw
)

const DrawAfter = 50

// Game holds the board and turn state. Start creates the initial game.
// Actions return the next game as a value.
type Game struct {
	board        Board
	whiteReserve uint8
	blackReserve uint8
	turn         Player
	pending      bool
	quiet        uint8
}

//golean:verify startRules : Start.«field:turn» = 1 ∧ Start.«field:whiteReserve» = 9 ∧ Start.«field:blackReserve» = 9 ∧
//golean:verify+   Start.«field:pending» = false ∧ Start.«field:quiet» = 0 ∧
//golean:verify+   ∀ p, «Board$stoneAt» Start.«field:board» p = 0
//golean:verify startIsValid : «Game$IsValid» Start = true
func Start() Game {
	return Game{
		board:        emptyBoard(),
		whiteReserve: 9,
		blackReserve: 9,
		turn:         White,
		pending:      false,
		quiet:        0,
	}
}

// IsValid reports whether the game has an initialized active player.
// Start creates a game that passes this check.
//
//golean:verify validTurn : ∀ s, «Game$IsValid» s = true ↔ s.«field:turn» = 1 ∨ s.«field:turn» = 2
func (state Game) IsValid() bool {
	return state.turn == White || state.turn == Black
}

//golean:verify boardSnapshot : ∀ s, «Game$Board» s = s.«field:board»
func (state Game) Board() Board { return state.board }

//golean:verify currentTurn : ∀ s, «Game$Turn» s = s.«field:turn»
func (state Game) Turn() Player { return state.turn }

//golean:verify pendingCapture : ∀ s, «Game$Pending» s = s.«field:pending»
func (state Game) Pending() bool { return state.pending }

//golean:verify placementPhase : ∀ s, «Game$Placing» s = true ↔
//golean:verify+   s.«field:whiteReserve» ≠ 0 ∨ s.«field:blackReserve» ≠ 0
func (state Game) Placing() bool {
	return state.whiteReserve != 0 || state.blackReserve != 0
}

func (state Game) reserve() uint8 {
	if state.turn == White {
		return state.whiteReserve
	}
	return state.blackReserve
}

func opponent(player Player) Player {
	if player == White {
		return Black
	}
	return White
}

func winner(player Player) Result {
	if player == White {
		return WhiteWins
	}
	return BlackWins
}

//golean:verify movementAvailability : ∀ b player, «Board$hasMove» b player = true ↔
//golean:verify+   («Board$count» b player = 3 ∧ «Board$count» b 0 ≠ 0) ∨ (3 < «Board$count» b player ∧ «Board$hasSlide» b player = true)
func (board Board) hasMove(player Player) bool {
	stones := board.count(player)
	if stones < 3 {
		return false
	}
	if stones == 3 {
		return board.count(Empty) != 0
	}
	return board.hasSlide(player)
}

// Outcome checks the player to move after placement and any pending capture.
// A win takes precedence over the quiet-move draw.
//
//golean:verify outcomeRules : ∀ s, «Game$Outcome» s =
//golean:verify+   if s.«field:pending» = true ∨ s.«field:whiteReserve» ≠ 0 ∨ s.«field:blackReserve» ≠ 0 then 0
//golean:verify+   else if «Board$hasMove» s.«field:board» s.«field:turn» = false then (if s.«field:turn» = 1 then 2 else 1)
//golean:verify+   else if 50 ≤ s.«field:quiet» then 3 else 0
func (state Game) Outcome() Result {
	if state.pending || state.Placing() {
		return Ongoing
	}
	if !state.board.hasMove(state.turn) {
		return winner(opponent(state.turn))
	}
	if state.quiet >= DrawAfter {
		return Draw
	}
	return Ongoing
}

//golean:verify placementLegality : ∀ s p, «Game$canPlace» s p = true ↔
//golean:verify+   «Game$IsValid» s = true ∧ s.«field:pending» = false ∧ (if s.«field:turn» = 1 then s.«field:whiteReserve» else s.«field:blackReserve») ≠ 0 ∧
//golean:verify+   p < 24 ∧ «Board$stoneAt» s.«field:board» p = 0
func (state Game) canPlace(to uint) bool {
	return state.IsValid() && !state.pending && state.reserve() != 0 &&
		to < Points && state.board.stoneAt(to) == Empty
}

//golean:verify movementLegality : ∀ s f t, «Game$canMove» s f t = true ↔
//golean:verify+   «Game$IsValid» s = true ∧ s.«field:pending» = false ∧ s.«field:whiteReserve» = 0 ∧ s.«field:blackReserve» = 0 ∧ s.«field:quiet» < 50 ∧
//golean:verify+   «Board$hasMove» s.«field:board» s.«field:turn» = true ∧ f < 24 ∧ t < 24 ∧
//golean:verify+   «Board$stoneAt» s.«field:board» f = s.«field:turn» ∧ «Board$stoneAt» s.«field:board» t = 0 ∧
//golean:verify+   («Board$count» s.«field:board» s.«field:turn» = 3 ∨ adjacent f t = true)
func (state Game) canMove(from, to uint) bool {
	return state.IsValid() && !state.pending && !state.Placing() && state.Outcome() == Ongoing &&
		from < Points && to < Points &&
		state.board.stoneAt(from) == state.turn && state.board.stoneAt(to) == Empty &&
		(state.board.count(state.turn) == 3 || adjacent(from, to))
}

//golean:verify captureLegality : ∀ s p, let other : UInt8 := if s.«field:turn» = 1 then 2 else 1
//golean:verify+   «Game$canCapture» s p = true ↔ «Game$IsValid» s = true ∧ s.«field:pending» = true ∧ p < 24 ∧ «Board$stoneAt» s.«field:board» p = other ∧
//golean:verify+   («Board$inMill» s.«field:board» p other = false ∨ «Board$hasUnprotected» s.«field:board» other = false)
func (state Game) canCapture(point uint) bool {
	other := opponent(state.turn)
	return state.IsValid() && state.pending && point < Points && state.board.stoneAt(point) == other &&
		(!state.board.inMill(point, other) || !state.board.hasUnprotected(other))
}

//golean:verify finishingTurn : ∀ s p, «Game$finishAction» s p =
//golean:verify+   let other : UInt8 := if s.«field:turn» = 1 then 2 else 1
//golean:verify+   if «Board$inMill» s.«field:board» p s.«field:turn» = true ∧ «Board$count» s.«field:board» other ≠ 0
//golean:verify+   then {s with «field:pending» := true} else {s with «field:turn» := other}
func (state Game) finishAction(to uint) Game {
	if state.board.inMill(to, state.turn) &&
		state.board.count(opponent(state.turn)) != 0 {
		return Game{
			board:        state.board,
			whiteReserve: state.whiteReserve,
			blackReserve: state.blackReserve,
			turn:         state.turn,
			pending:      true,
			quiet:        state.quiet,
		}
	}
	return Game{
		board:        state.board,
		whiteReserve: state.whiteReserve,
		blackReserve: state.blackReserve,
		turn:         opponent(state.turn),
		pending:      state.pending,
		quiet:        state.quiet,
	}
}

// Place adds a reserve stone. A newly closed mill may leave a capture pending.
//
//golean:verify placeTransition : ∀ s p, «Game$place» s p = if «Game$canPlace» s p then
//golean:verify+   let placed := {s with «field:board» := «Board$setPoint» s.«field:board» p s.«field:turn»}
//golean:verify+   (ActionResult.mk («Game$finishAction» (if s.«field:turn» = 1 then {placed with «field:whiteReserve» := s.«field:whiteReserve» - 1}
//golean:verify+   else {placed with «field:blackReserve» := s.«field:blackReserve» - 1}) p) true)
//golean:verify+   else ⟨s, false⟩
//golean:verify placePreservesValidity : ∀ s p, «Game$IsValid» s = true → «Game$IsValid» («Game$place» s p).«field:next» = true
func (state Game) place(to uint) ActionResult {
	if !state.canPlace(to) {
		return ActionResult{next: state, accepted: false}
	}
	board := state.board.setPoint(to, state.turn)
	if state.turn == White {
		return ActionResult{next: (Game{
			board:        board,
			whiteReserve: state.whiteReserve - 1,
			blackReserve: state.blackReserve,
			turn:         state.turn,
			pending:      state.pending,
			quiet:        state.quiet,
		}).finishAction(to), accepted: true}
	}
	return ActionResult{next: (Game{
		board:        board,
		whiteReserve: state.whiteReserve,
		blackReserve: state.blackReserve - 1,
		turn:         state.turn,
		pending:      state.pending,
		quiet:        state.quiet,
	}).finishAction(to), accepted: true}
}

// Move slides a stone or flies when the current player has exactly three.
//
//golean:verify moveTransition : ∀ s f t, «Game$move» s f t = if «Game$canMove» s f t then
//golean:verify+   let board := «Board$setPoint» («Board$setPoint» s.«field:board» f 0) t s.«field:turn»
//golean:verify+   (ActionResult.mk («Game$finishAction» {s with «field:board» := board, «field:quiet» := s.«field:quiet» + 1} t) true) else ⟨s, false⟩
//golean:verify movePreservesOpposingStones : ∀ s f t p,
//golean:verify+   s.«field:turn» = 1 ∨ s.«field:turn» = 2 →
//golean:verify+   («Game$move» s f t).«field:accepted» = true → p < 24 →
//golean:verify+   «Board$stoneAt» («Game$Board» s) p = opponent s.«field:turn» →
//golean:verify+   «Board$stoneAt» («Game$Board» («Game$move» s f t).«field:next») p = opponent s.«field:turn»
//golean:verify moveGrantsCaptureExactlyOnMill : ∀ s f t, («Game$move» s f t).«field:accepted» = true →
//golean:verify+   let next := («Game$move» s f t).«field:next»
//golean:verify+   «Game$Pending» next = true ↔
//golean:verify+   «Board$inMill» («Game$Board» next) t s.«field:turn» = true ∧
//golean:verify+   «Board$count» («Game$Board» next) (opponent s.«field:turn») ≠ 0
//golean:verify movePreservesValidity : ∀ s f t, «Game$IsValid» s = true → «Game$IsValid» («Game$move» s f t).«field:next» = true
func (state Game) move(from, to uint) ActionResult {
	if !state.canMove(from, to) {
		return ActionResult{next: state, accepted: false}
	}
	board := state.board.setPoint(from, Empty).setPoint(to, state.turn)
	next := Game{
		board:        board,
		whiteReserve: state.whiteReserve,
		blackReserve: state.blackReserve,
		turn:         state.turn,
		pending:      state.pending,
		quiet:        state.quiet + 1,
	}
	return ActionResult{next: next.finishAction(to), accepted: true}
}

// Capture removes one opponent stone and completes a turn.
//
//golean:verify captureTransition : ∀ s p, «Game$capture» s p = if «Game$canCapture» s p then
//golean:verify+   let turn := if s.«field:turn» = 1 then 2 else 1
//golean:verify+   (ActionResult.mk {s with «field:board» := «Board$setPoint» s.«field:board» p 0, «field:pending» := false, «field:quiet» := 0, «field:turn» := turn} true)
//golean:verify+   else ⟨s, false⟩
//golean:verify capturePreservesValidity : ∀ s p, «Game$IsValid» s = true → «Game$IsValid» («Game$capture» s p).«field:next» = true
func (state Game) capture(point uint) ActionResult {
	if !state.canCapture(point) {
		return ActionResult{next: state, accepted: false}
	}
	return ActionResult{next: Game{
		board:        state.board.setPoint(point, Empty),
		whiteReserve: state.whiteReserve,
		blackReserve: state.blackReserve,
		turn:         opponent(state.turn),
		pending:      false,
		quiet:        0,
	}, accepted: true}
}

// ActionResult packages the two observations of a modeled transition.
type ActionResult struct {
	next     Game
	accepted bool
}

type Point uint8
type Player uint8

const (
	Empty Player = iota
	White
	Black
)

const Points = 24

// Board stores three rings outermost first, clockwise from each top-left corner.
type Board struct {
	points lean.Array[Player]
}

func emptyBoard() Board {
	points := lean.Array[Player]{}.Push(Empty).Push(Empty).Push(Empty).Push(Empty).
		Push(Empty).Push(Empty).Push(Empty).Push(Empty).
		Push(Empty).Push(Empty).Push(Empty).Push(Empty).
		Push(Empty).Push(Empty).Push(Empty).Push(Empty).
		Push(Empty).Push(Empty).Push(Empty).Push(Empty).
		Push(Empty).Push(Empty).Push(Empty).Push(Empty)
	return Board{points: points}
}

// At returns the stone at point, or Empty for a vacant or out-of-range point.
//
//golean:verify outsideBoardIsEmpty : ∀ b p, 24 ≤ p → «Board$stoneAt» b p = 0
func (board Board) stoneAt(point uint) Player {
	if point >= Points {
		return Empty
	}
	return board.points.Get(point).UnwrapOr(Empty)
}

//golean:verify boardUpdate : ∀ b p q player, p < 24 → q < 24 → (p = q → p.toNat < b.«field:points».size) →
//golean:verify+   «Board$stoneAt» («Board$setPoint» b p player) q = if q = p then player else «Board$stoneAt» b q
func (board Board) setPoint(point uint, player Player) Board {
	if point < Points {
		return Board{points: board.points.Set(point, player)}
	}
	return board
}

// adjacent reports whether two points share a single board edge.
//
//golean:verify boardEdges : ∀ a b : Fin 24,
//golean:verify+   adjacent (UInt64.ofNat a.val) (UInt64.ofNat b.val) =
//golean:verify+   decide ((a.val / 8 = b.val / 8 ∧ ((a.val + 1) % 8 = b.val % 8 ∨ (b.val + 1) % 8 = a.val % 8)) ∨
//golean:verify+     (a.val % 8 = b.val % 8 ∧ a.val % 2 = 1 ∧ (a.val / 8 + 1 = b.val / 8 ∨ b.val / 8 + 1 = a.val / 8)))
func adjacent(from, to uint) bool {
	if from == 0 {
		return to == 7 || to == 1
	}
	if from == 1 {
		return to == 0 || to == 2 || to == 9
	}
	if from == 2 {
		return to == 1 || to == 3
	}
	if from == 3 {
		return to == 2 || to == 4 || to == 11
	}
	if from == 4 {
		return to == 3 || to == 5
	}
	if from == 5 {
		return to == 4 || to == 6 || to == 13
	}
	if from == 6 {
		return to == 5 || to == 7
	}
	if from == 7 {
		return to == 6 || to == 0 || to == 15
	}
	if from == 8 {
		return to == 15 || to == 9
	}
	if from == 9 {
		return to == 8 || to == 10 || to == 1 || to == 17
	}
	if from == 10 {
		return to == 9 || to == 11
	}
	if from == 11 {
		return to == 10 || to == 12 || to == 3 || to == 19
	}
	if from == 12 {
		return to == 11 || to == 13
	}
	if from == 13 {
		return to == 12 || to == 14 || to == 5 || to == 21
	}
	if from == 14 {
		return to == 13 || to == 15
	}
	if from == 15 {
		return to == 14 || to == 8 || to == 7 || to == 23
	}
	if from == 16 {
		return to == 23 || to == 17
	}
	if from == 17 {
		return to == 16 || to == 18 || to == 9
	}
	if from == 18 {
		return to == 17 || to == 19
	}
	if from == 19 {
		return to == 18 || to == 20 || to == 11
	}
	if from == 20 {
		return to == 19 || to == 21
	}
	if from == 21 {
		return to == 20 || to == 22 || to == 13
	}
	if from == 22 {
		return to == 21 || to == 23
	}
	if from == 23 {
		return to == 22 || to == 16 || to == 15
	}
	return false
}

// inMill checks the lines through point for the player occupying it.
//
//golean:verify millGeometry : ∀ board p (player : UInt8), p < 24 → player ≠ 0 →
//golean:verify+   let lines : List (List UInt64) := [[0,1,2], [2,3,4], [4,5,6], [6,7,0],
//golean:verify+     [8,9,10], [10,11,12], [12,13,14], [14,15,8], [16,17,18], [18,19,20],
//golean:verify+     [20,21,22], [22,23,16], [1,9,17], [3,11,19], [5,13,21], [7,15,23]]
//golean:verify+   «Board$inMill» board p player = lines.any (fun line => line.contains p && line.all (fun q => «Board$stoneAt» board q == player))
func (board Board) inMill(point uint, player Player) bool {
	if player == Empty || board.stoneAt(point) != player {
		return false
	}
	if point == 0 {
		return board.stoneAt(1) == player && board.stoneAt(2) == player ||
			board.stoneAt(6) == player && board.stoneAt(7) == player
	}
	if point == 1 {
		return board.stoneAt(0) == player && board.stoneAt(2) == player ||
			board.stoneAt(9) == player && board.stoneAt(17) == player
	}
	if point == 2 {
		return board.stoneAt(0) == player && board.stoneAt(1) == player ||
			board.stoneAt(3) == player && board.stoneAt(4) == player
	}
	if point == 3 {
		return board.stoneAt(2) == player && board.stoneAt(4) == player ||
			board.stoneAt(11) == player && board.stoneAt(19) == player
	}
	if point == 4 {
		return board.stoneAt(2) == player && board.stoneAt(3) == player ||
			board.stoneAt(5) == player && board.stoneAt(6) == player
	}
	if point == 5 {
		return board.stoneAt(4) == player && board.stoneAt(6) == player ||
			board.stoneAt(13) == player && board.stoneAt(21) == player
	}
	if point == 6 {
		return board.stoneAt(4) == player && board.stoneAt(5) == player ||
			board.stoneAt(7) == player && board.stoneAt(0) == player
	}
	if point == 7 {
		return board.stoneAt(6) == player && board.stoneAt(0) == player ||
			board.stoneAt(15) == player && board.stoneAt(23) == player
	}
	if point == 8 {
		return board.stoneAt(9) == player && board.stoneAt(10) == player ||
			board.stoneAt(14) == player && board.stoneAt(15) == player
	}
	if point == 9 {
		return board.stoneAt(8) == player && board.stoneAt(10) == player ||
			board.stoneAt(1) == player && board.stoneAt(17) == player
	}
	if point == 10 {
		return board.stoneAt(8) == player && board.stoneAt(9) == player ||
			board.stoneAt(11) == player && board.stoneAt(12) == player
	}
	if point == 11 {
		return board.stoneAt(10) == player && board.stoneAt(12) == player ||
			board.stoneAt(3) == player && board.stoneAt(19) == player
	}
	if point == 12 {
		return board.stoneAt(10) == player && board.stoneAt(11) == player ||
			board.stoneAt(13) == player && board.stoneAt(14) == player
	}
	if point == 13 {
		return board.stoneAt(12) == player && board.stoneAt(14) == player ||
			board.stoneAt(5) == player && board.stoneAt(21) == player
	}
	if point == 14 {
		return board.stoneAt(12) == player && board.stoneAt(13) == player ||
			board.stoneAt(15) == player && board.stoneAt(8) == player
	}
	if point == 15 {
		return board.stoneAt(14) == player && board.stoneAt(8) == player ||
			board.stoneAt(7) == player && board.stoneAt(23) == player
	}
	if point == 16 {
		return board.stoneAt(17) == player && board.stoneAt(18) == player ||
			board.stoneAt(22) == player && board.stoneAt(23) == player
	}
	if point == 17 {
		return board.stoneAt(16) == player && board.stoneAt(18) == player ||
			board.stoneAt(1) == player && board.stoneAt(9) == player
	}
	if point == 18 {
		return board.stoneAt(16) == player && board.stoneAt(17) == player ||
			board.stoneAt(19) == player && board.stoneAt(20) == player
	}
	if point == 19 {
		return board.stoneAt(18) == player && board.stoneAt(20) == player ||
			board.stoneAt(3) == player && board.stoneAt(11) == player
	}
	if point == 20 {
		return board.stoneAt(18) == player && board.stoneAt(19) == player ||
			board.stoneAt(21) == player && board.stoneAt(22) == player
	}
	if point == 21 {
		return board.stoneAt(20) == player && board.stoneAt(22) == player ||
			board.stoneAt(5) == player && board.stoneAt(13) == player
	}
	if point == 22 {
		return board.stoneAt(20) == player && board.stoneAt(21) == player ||
			board.stoneAt(23) == player && board.stoneAt(16) == player
	}
	if point == 23 {
		return board.stoneAt(22) == player && board.stoneAt(16) == player ||
			board.stoneAt(7) == player && board.stoneAt(15) == player
	}
	return false
}

// count reports how many board points are occupied by player (or are empty
// when player is Empty).
//
//golean:verify countedStones : ∀ b player,
//golean:verify+   let points := (List.range 24).map UInt64.ofNat
//golean:verify+   «Board$count» b player = (points.map (fun p => if «Board$stoneAt» b p = player then 1 else 0)).foldl (· + ·) 0
func (board Board) count(player Player) uint8 {
	return matches(board.stoneAt(0), player) +
		matches(board.stoneAt(1), player) +
		matches(board.stoneAt(2), player) +
		matches(board.stoneAt(3), player) +
		matches(board.stoneAt(4), player) +
		matches(board.stoneAt(5), player) +
		matches(board.stoneAt(6), player) +
		matches(board.stoneAt(7), player) +
		matches(board.stoneAt(8), player) +
		matches(board.stoneAt(9), player) +
		matches(board.stoneAt(10), player) +
		matches(board.stoneAt(11), player) +
		matches(board.stoneAt(12), player) +
		matches(board.stoneAt(13), player) +
		matches(board.stoneAt(14), player) +
		matches(board.stoneAt(15), player) +
		matches(board.stoneAt(16), player) +
		matches(board.stoneAt(17), player) +
		matches(board.stoneAt(18), player) +
		matches(board.stoneAt(19), player) +
		matches(board.stoneAt(20), player) +
		matches(board.stoneAt(21), player) +
		matches(board.stoneAt(22), player) +
		matches(board.stoneAt(23), player)
}

func matches(cell, player Player) uint8 {
	if cell == player {
		return 1
	}
	return 0
}

//golean:verify unprotectedStones : ∀ b player,
//golean:verify+   let points := (List.range 24).map UInt64.ofNat
//golean:verify+   «Board$hasUnprotected» b player = points.any (fun p => decide («Board$stoneAt» b p = player) && !«Board$inMill» b p player)
func (board Board) hasUnprotected(player Player) bool {
	return board.unprotected(0, player) ||
		board.unprotected(1, player) ||
		board.unprotected(2, player) ||
		board.unprotected(3, player) ||
		board.unprotected(4, player) ||
		board.unprotected(5, player) ||
		board.unprotected(6, player) ||
		board.unprotected(7, player) ||
		board.unprotected(8, player) ||
		board.unprotected(9, player) ||
		board.unprotected(10, player) ||
		board.unprotected(11, player) ||
		board.unprotected(12, player) ||
		board.unprotected(13, player) ||
		board.unprotected(14, player) ||
		board.unprotected(15, player) ||
		board.unprotected(16, player) ||
		board.unprotected(17, player) ||
		board.unprotected(18, player) ||
		board.unprotected(19, player) ||
		board.unprotected(20, player) ||
		board.unprotected(21, player) ||
		board.unprotected(22, player) ||
		board.unprotected(23, player)
}

func (board Board) unprotected(point uint, player Player) bool {
	return board.stoneAt(point) == player && !board.inMill(point, player)
}

//golean:verify slideAvailability : ∀ b player,
//golean:verify+   let points := (List.range 24).map UInt64.ofNat
//golean:verify+   «Board$hasSlide» b player = points.any (fun f => decide («Board$stoneAt» b f = player) &&
//golean:verify+     points.any (fun t => decide («Board$stoneAt» b t = 0) && adjacent f t))
func (board Board) hasSlide(player Player) bool {
	return board.hasSlideFrom(0, player) ||
		board.hasSlideFrom(1, player) ||
		board.hasSlideFrom(2, player) ||
		board.hasSlideFrom(3, player) ||
		board.hasSlideFrom(4, player) ||
		board.hasSlideFrom(5, player) ||
		board.hasSlideFrom(6, player) ||
		board.hasSlideFrom(7, player) ||
		board.hasSlideFrom(8, player) ||
		board.hasSlideFrom(9, player) ||
		board.hasSlideFrom(10, player) ||
		board.hasSlideFrom(11, player) ||
		board.hasSlideFrom(12, player) ||
		board.hasSlideFrom(13, player) ||
		board.hasSlideFrom(14, player) ||
		board.hasSlideFrom(15, player) ||
		board.hasSlideFrom(16, player) ||
		board.hasSlideFrom(17, player) ||
		board.hasSlideFrom(18, player) ||
		board.hasSlideFrom(19, player) ||
		board.hasSlideFrom(20, player) ||
		board.hasSlideFrom(21, player) ||
		board.hasSlideFrom(22, player) ||
		board.hasSlideFrom(23, player)
}

func (board Board) hasSlideFrom(point uint, player Player) bool {
	return board.stoneAt(point) == player && board.hasExit(point)
}

func (board Board) hasExit(point uint) bool {
	if point == 0 {
		return board.stoneAt(7) == Empty || board.stoneAt(1) == Empty
	}
	if point == 1 {
		return board.stoneAt(0) == Empty || board.stoneAt(2) == Empty || board.stoneAt(9) == Empty
	}
	if point == 2 {
		return board.stoneAt(1) == Empty || board.stoneAt(3) == Empty
	}
	if point == 3 {
		return board.stoneAt(2) == Empty || board.stoneAt(4) == Empty || board.stoneAt(11) == Empty
	}
	if point == 4 {
		return board.stoneAt(3) == Empty || board.stoneAt(5) == Empty
	}
	if point == 5 {
		return board.stoneAt(4) == Empty || board.stoneAt(6) == Empty || board.stoneAt(13) == Empty
	}
	if point == 6 {
		return board.stoneAt(5) == Empty || board.stoneAt(7) == Empty
	}
	if point == 7 {
		return board.stoneAt(6) == Empty || board.stoneAt(0) == Empty || board.stoneAt(15) == Empty
	}
	if point == 8 {
		return board.stoneAt(15) == Empty || board.stoneAt(9) == Empty
	}
	if point == 9 {
		return board.stoneAt(8) == Empty || board.stoneAt(10) == Empty || board.stoneAt(1) == Empty || board.stoneAt(17) == Empty
	}
	if point == 10 {
		return board.stoneAt(9) == Empty || board.stoneAt(11) == Empty
	}
	if point == 11 {
		return board.stoneAt(10) == Empty || board.stoneAt(12) == Empty || board.stoneAt(3) == Empty || board.stoneAt(19) == Empty
	}
	if point == 12 {
		return board.stoneAt(11) == Empty || board.stoneAt(13) == Empty
	}
	if point == 13 {
		return board.stoneAt(12) == Empty || board.stoneAt(14) == Empty || board.stoneAt(5) == Empty || board.stoneAt(21) == Empty
	}
	if point == 14 {
		return board.stoneAt(13) == Empty || board.stoneAt(15) == Empty
	}
	if point == 15 {
		return board.stoneAt(14) == Empty || board.stoneAt(8) == Empty || board.stoneAt(7) == Empty || board.stoneAt(23) == Empty
	}
	if point == 16 {
		return board.stoneAt(23) == Empty || board.stoneAt(17) == Empty
	}
	if point == 17 {
		return board.stoneAt(16) == Empty || board.stoneAt(18) == Empty || board.stoneAt(9) == Empty
	}
	if point == 18 {
		return board.stoneAt(17) == Empty || board.stoneAt(19) == Empty
	}
	if point == 19 {
		return board.stoneAt(18) == Empty || board.stoneAt(20) == Empty || board.stoneAt(11) == Empty
	}
	if point == 20 {
		return board.stoneAt(19) == Empty || board.stoneAt(21) == Empty
	}
	if point == 21 {
		return board.stoneAt(20) == Empty || board.stoneAt(22) == Empty || board.stoneAt(13) == Empty
	}
	if point == 22 {
		return board.stoneAt(21) == Empty || board.stoneAt(23) == Empty
	}
	if point == 23 {
		return board.stoneAt(22) == Empty || board.stoneAt(16) == Empty || board.stoneAt(15) == Empty
	}
	return false
}

// The public methods adapt the modeled functions to the legacy signatures.
func (state Game) CanPlace(to Point) bool {
	return state.canPlace(uint(to))
}

func (state Game) CanMove(from, to Point) bool {
	return state.canMove(uint(from), uint(to))
}

func (state Game) CanCapture(at Point) bool {
	return state.canCapture(uint(at))
}

func (state Game) Place(to Point) (Game, bool) {
	result := state.place(uint(to))
	return result.next, result.accepted
}

func (state Game) Move(from, to Point) (Game, bool) {
	result := state.move(uint(from), uint(to))
	return result.next, result.accepted
}

func (state Game) Capture(at Point) (Game, bool) {
	result := state.capture(uint(at))
	return result.next, result.accepted
}

func (board Board) At(point Point) Player {
	return board.stoneAt(uint(point))
}
