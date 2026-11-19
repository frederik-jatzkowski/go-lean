// Package morris implements the rules of a two-player Nine Men's Morris game.
//
//golean:verify:import nine_mens_morris.morris_rules
//golean:verify fromStartMatchesRules : ∀ (actions : List Rules.Action),
//golean:verify+   (Start, «Game$Outcome» Start, Rules.history act «Game$Outcome» Start actions) =
//golean:verify+     (Rules.initial, Rules.outcome Rules.initial,
//golean:verify+       Rules.history Rules.step Rules.outcome Rules.initial actions)
package morris

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
//golean:verify+   ∀ p, «Board$At» Start.«field:board» p = 0
//golean:verify startIsValid : «Game$IsValid» Start = true
func Start() Game {
	return Game{whiteReserve: 9, blackReserve: 9, turn: White}
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

//golean:verify movementAvailability : ∀ b player, hasMove b player = true ↔
//golean:verify+   (count b player = 3 ∧ count b 0 ≠ 0) ∨ (3 < count b player ∧ hasSlide b player = true)
func hasMove(board Board, player Player) bool {
	stones := count(board, player)
	if stones < 3 {
		return false
	}
	if stones == 3 {
		return count(board, Empty) != 0
	}
	return hasSlide(board, player)
}

// Outcome checks the player to move after placement and any pending capture.
// A win takes precedence over the quiet-move draw.
//
//golean:verify outcomeRules : ∀ s, «Game$Outcome» s =
//golean:verify+   if s.«field:pending» = true ∨ s.«field:whiteReserve» ≠ 0 ∨ s.«field:blackReserve» ≠ 0 then 0
//golean:verify+   else if hasMove s.«field:board» s.«field:turn» = false then (if s.«field:turn» = 1 then 2 else 1)
//golean:verify+   else if 50 ≤ s.«field:quiet» then 3 else 0
func (state Game) Outcome() Result {
	if state.pending || state.Placing() {
		return Ongoing
	}
	if !hasMove(state.board, state.turn) {
		return winner(opponent(state.turn))
	}
	if state.quiet >= DrawAfter {
		return Draw
	}
	return Ongoing
}

//golean:verify placementLegality : ∀ s p, «Game$CanPlace» s p = true ↔
//golean:verify+   «Game$IsValid» s = true ∧ s.«field:pending» = false ∧ (if s.«field:turn» = 1 then s.«field:whiteReserve» else s.«field:blackReserve») ≠ 0 ∧
//golean:verify+   p < 24 ∧ «Board$At» s.«field:board» p = 0
func (state Game) CanPlace(to Point) bool {
	return state.IsValid() && !state.pending && state.reserve() != 0 &&
		to < Points && state.board.At(to) == Empty
}

//golean:verify movementLegality : ∀ s f t, «Game$CanMove» s f t = true ↔
//golean:verify+   «Game$IsValid» s = true ∧ s.«field:pending» = false ∧ s.«field:whiteReserve» = 0 ∧ s.«field:blackReserve» = 0 ∧ s.«field:quiet» < 50 ∧
//golean:verify+   hasMove s.«field:board» s.«field:turn» = true ∧ f < 24 ∧ t < 24 ∧
//golean:verify+   «Board$At» s.«field:board» f = s.«field:turn» ∧ «Board$At» s.«field:board» t = 0 ∧
//golean:verify+   (count s.«field:board» s.«field:turn» = 3 ∨ adjacent f t = true)
func (state Game) CanMove(from, to Point) bool {
	return state.IsValid() && !state.pending && !state.Placing() && state.Outcome() == Ongoing &&
		from < Points && to < Points &&
		state.board.At(from) == state.turn && state.board.At(to) == Empty &&
		(count(state.board, state.turn) == 3 || adjacent(from, to))
}

//golean:verify captureLegality : ∀ s p, let other : UInt8 := if s.«field:turn» = 1 then 2 else 1
//golean:verify+   «Game$CanCapture» s p = true ↔ «Game$IsValid» s = true ∧ s.«field:pending» = true ∧ p < 24 ∧ «Board$At» s.«field:board» p = other ∧
//golean:verify+   (inMill s.«field:board» p other = false ∨ hasUnprotected s.«field:board» other = false)
func (state Game) CanCapture(at Point) bool {
	other := opponent(state.turn)
	return state.IsValid() && state.pending && at < Points && state.board.At(at) == other &&
		(!inMill(state.board, at, other) || !hasUnprotected(state.board, other))
}

//golean:verify finishingTurn : ∀ s p, «Game$finishAction» s p =
//golean:verify+   let other : UInt8 := if s.«field:turn» = 1 then 2 else 1
//golean:verify+   if inMill s.«field:board» p s.«field:turn» = true ∧ count s.«field:board» other ≠ 0
//golean:verify+   then {s with «field:pending» := true} else {s with «field:turn» := other}
func (state Game) finishAction(to Point) Game {
	if inMill(state.board, to, state.turn) &&
		count(state.board, opponent(state.turn)) != 0 {
		state.pending = true
		return state
	}
	state.turn = opponent(state.turn)
	return state
}

// Place adds a reserve stone. A newly closed mill may leave a capture pending.
//
//golean:verify placeTransition : ∀ s p, «Game$Place» s p = if «Game$CanPlace» s p then
//golean:verify+   let placed := {s with «field:board» := setPoint s.«field:board» p s.«field:turn»}
//golean:verify+   («Game$finishAction» (if s.«field:turn» = 1 then {placed with «field:whiteReserve» := s.«field:whiteReserve» - 1}
//golean:verify+   else {placed with «field:blackReserve» := s.«field:blackReserve» - 1}) p, true)
//golean:verify+   else (s, false)
//golean:verify placePreservesValidity : ∀ s p, «Game$IsValid» s = true → «Game$IsValid» («Game$Place» s p).1 = true
func (state Game) Place(to Point) (Game, bool) {
	if !state.CanPlace(to) {
		return state, false
	}
	state.board = setPoint(state.board, to, state.turn)
	if state.turn == White {
		state.whiteReserve--
	} else {
		state.blackReserve--
	}
	return state.finishAction(to), true
}

// Move slides a stone or flies when the current player has exactly three.
//
//golean:verify moveTransition : ∀ s f t, «Game$Move» s f t = if «Game$CanMove» s f t then
//golean:verify+   let board := setPoint (setPoint s.«field:board» f 0) t s.«field:turn»
//golean:verify+   («Game$finishAction» {s with «field:board» := board, «field:quiet» := s.«field:quiet» + 1} t, true) else (s, false)
//golean:verify movePreservesOpposingStones : ∀ s f t p,
//golean:verify+   s.«field:turn» = 1 ∨ s.«field:turn» = 2 →
//golean:verify+   («Game$Move» s f t).2 = true → p < 24 →
//golean:verify+   «Board$At» («Game$Board» s) p = opponent s.«field:turn» →
//golean:verify+   «Board$At» («Game$Board» («Game$Move» s f t).1) p = opponent s.«field:turn»
//golean:verify moveGrantsCaptureExactlyOnMill : ∀ s f t, («Game$Move» s f t).2 = true →
//golean:verify+   let next := («Game$Move» s f t).1
//golean:verify+   «Game$Pending» next = true ↔
//golean:verify+   inMill («Game$Board» next) t s.«field:turn» = true ∧
//golean:verify+   count («Game$Board» next) (opponent s.«field:turn») ≠ 0
//golean:verify movePreservesValidity : ∀ s f t, «Game$IsValid» s = true → «Game$IsValid» («Game$Move» s f t).1 = true
func (state Game) Move(from, to Point) (Game, bool) {
	if !state.CanMove(from, to) {
		return state, false
	}
	state.board = setPoint(setPoint(state.board, from, Empty), to, state.turn)
	state.quiet++
	return state.finishAction(to), true
}

// Capture removes one opponent stone and completes a turn.
//
//golean:verify captureTransition : ∀ s p, «Game$Capture» s p = if «Game$CanCapture» s p then
//golean:verify+   let turn := if s.«field:turn» = 1 then 2 else 1
//golean:verify+   ({s with «field:board» := setPoint s.«field:board» p 0, «field:pending» := false, «field:quiet» := 0, «field:turn» := turn}, true)
//golean:verify+   else (s, false)
//golean:verify capturePreservesValidity : ∀ s p, «Game$IsValid» s = true → «Game$IsValid» («Game$Capture» s p).1 = true
func (state Game) Capture(at Point) (Game, bool) {
	if !state.CanCapture(at) {
		return state, false
	}
	state.board = setPoint(state.board, at, Empty)
	state.pending = false
	state.quiet = 0
	state.turn = opponent(state.turn)
	return state, true
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
	points [Points]Player
}

// At returns the stone at point, or Empty for a vacant or out-of-range point.
//
//golean:verify outsideBoardIsEmpty : ∀ b p, 24 ≤ p → «Board$At» b p = 0
func (board Board) At(point Point) Player {
	if point >= Points {
		return Empty
	}
	return board.points[point]
}

//golean:verify boardUpdate : ∀ b p q player, p < 24 → q < 24 →
//golean:verify+   «Board$At» (setPoint b p player) q = if q = p then player else «Board$At» b q
func setPoint(board Board, point Point, player Player) Board {
	if point < Points {
		board.points[point] = player
	}
	return board
}

// adjacent reports whether two points share a single board edge.
//
//golean:verify boardEdges : ∀ a b : Fin 24,
//golean:verify+   adjacent (UInt8.ofNat a.val) (UInt8.ofNat b.val) =
//golean:verify+   decide ((a.val / 8 = b.val / 8 ∧ ((a.val + 1) % 8 = b.val % 8 ∨ (b.val + 1) % 8 = a.val % 8)) ∨
//golean:verify+     (a.val % 8 = b.val % 8 ∧ a.val % 2 = 1 ∧ (a.val / 8 + 1 = b.val / 8 ∨ b.val / 8 + 1 = a.val / 8)))
func adjacent(from, to Point) bool {
	switch from {
	case 0:
		return to == 7 || to == 1
	case 1:
		return to == 0 || to == 2 || to == 9
	case 2:
		return to == 1 || to == 3
	case 3:
		return to == 2 || to == 4 || to == 11
	case 4:
		return to == 3 || to == 5
	case 5:
		return to == 4 || to == 6 || to == 13
	case 6:
		return to == 5 || to == 7
	case 7:
		return to == 6 || to == 0 || to == 15
	case 8:
		return to == 15 || to == 9
	case 9:
		return to == 8 || to == 10 || to == 1 || to == 17
	case 10:
		return to == 9 || to == 11
	case 11:
		return to == 10 || to == 12 || to == 3 || to == 19
	case 12:
		return to == 11 || to == 13
	case 13:
		return to == 12 || to == 14 || to == 5 || to == 21
	case 14:
		return to == 13 || to == 15
	case 15:
		return to == 14 || to == 8 || to == 7 || to == 23
	case 16:
		return to == 23 || to == 17
	case 17:
		return to == 16 || to == 18 || to == 9
	case 18:
		return to == 17 || to == 19
	case 19:
		return to == 18 || to == 20 || to == 11
	case 20:
		return to == 19 || to == 21
	case 21:
		return to == 20 || to == 22 || to == 13
	case 22:
		return to == 21 || to == 23
	case 23:
		return to == 22 || to == 16 || to == 15
	default:
		return false
	}
}

// inMill checks the lines through point for the player occupying it.
//
//golean:verify millGeometry : ∀ board p (player : UInt8), p < 24 → player ≠ 0 →
//golean:verify+   let lines : List (List UInt8) := [[0,1,2], [2,3,4], [4,5,6], [6,7,0],
//golean:verify+     [8,9,10], [10,11,12], [12,13,14], [14,15,8], [16,17,18], [18,19,20],
//golean:verify+     [20,21,22], [22,23,16], [1,9,17], [3,11,19], [5,13,21], [7,15,23]]
//golean:verify+   inMill board p player = lines.any (fun line => line.contains p && line.all (fun q => «Board$At» board q == player))
func inMill(board Board, point Point, player Player) bool {
	if player == Empty || board.At(point) != player {
		return false
	}
	switch point {
	case 0:
		return board.points[1] == player && board.points[2] == player ||
			board.points[6] == player && board.points[7] == player
	case 1:
		return board.points[0] == player && board.points[2] == player ||
			board.points[9] == player && board.points[17] == player
	case 2:
		return board.points[0] == player && board.points[1] == player ||
			board.points[3] == player && board.points[4] == player
	case 3:
		return board.points[2] == player && board.points[4] == player ||
			board.points[11] == player && board.points[19] == player
	case 4:
		return board.points[2] == player && board.points[3] == player ||
			board.points[5] == player && board.points[6] == player
	case 5:
		return board.points[4] == player && board.points[6] == player ||
			board.points[13] == player && board.points[21] == player
	case 6:
		return board.points[4] == player && board.points[5] == player ||
			board.points[7] == player && board.points[0] == player
	case 7:
		return board.points[6] == player && board.points[0] == player ||
			board.points[15] == player && board.points[23] == player
	case 8:
		return board.points[9] == player && board.points[10] == player ||
			board.points[14] == player && board.points[15] == player
	case 9:
		return board.points[8] == player && board.points[10] == player ||
			board.points[1] == player && board.points[17] == player
	case 10:
		return board.points[8] == player && board.points[9] == player ||
			board.points[11] == player && board.points[12] == player
	case 11:
		return board.points[10] == player && board.points[12] == player ||
			board.points[3] == player && board.points[19] == player
	case 12:
		return board.points[10] == player && board.points[11] == player ||
			board.points[13] == player && board.points[14] == player
	case 13:
		return board.points[12] == player && board.points[14] == player ||
			board.points[5] == player && board.points[21] == player
	case 14:
		return board.points[12] == player && board.points[13] == player ||
			board.points[15] == player && board.points[8] == player
	case 15:
		return board.points[14] == player && board.points[8] == player ||
			board.points[7] == player && board.points[23] == player
	case 16:
		return board.points[17] == player && board.points[18] == player ||
			board.points[22] == player && board.points[23] == player
	case 17:
		return board.points[16] == player && board.points[18] == player ||
			board.points[1] == player && board.points[9] == player
	case 18:
		return board.points[16] == player && board.points[17] == player ||
			board.points[19] == player && board.points[20] == player
	case 19:
		return board.points[18] == player && board.points[20] == player ||
			board.points[3] == player && board.points[11] == player
	case 20:
		return board.points[18] == player && board.points[19] == player ||
			board.points[21] == player && board.points[22] == player
	case 21:
		return board.points[20] == player && board.points[22] == player ||
			board.points[5] == player && board.points[13] == player
	case 22:
		return board.points[20] == player && board.points[21] == player ||
			board.points[23] == player && board.points[16] == player
	case 23:
		return board.points[22] == player && board.points[16] == player ||
			board.points[7] == player && board.points[15] == player
	default:
		return false
	}
}

// count reports how many board points are occupied by player (or are empty
// when player is Empty).
//
//golean:verify countedStones : ∀ b player,
//golean:verify+   let points := (List.range 24).map UInt8.ofNat
//golean:verify+   count b player = (points.map (fun p => if «Board$At» b p = player then 1 else 0)).foldl (· + ·) 0
func count(board Board, player Player) uint8 {
	return matches(board.points[0], player) +
		matches(board.points[1], player) +
		matches(board.points[2], player) +
		matches(board.points[3], player) +
		matches(board.points[4], player) +
		matches(board.points[5], player) +
		matches(board.points[6], player) +
		matches(board.points[7], player) +
		matches(board.points[8], player) +
		matches(board.points[9], player) +
		matches(board.points[10], player) +
		matches(board.points[11], player) +
		matches(board.points[12], player) +
		matches(board.points[13], player) +
		matches(board.points[14], player) +
		matches(board.points[15], player) +
		matches(board.points[16], player) +
		matches(board.points[17], player) +
		matches(board.points[18], player) +
		matches(board.points[19], player) +
		matches(board.points[20], player) +
		matches(board.points[21], player) +
		matches(board.points[22], player) +
		matches(board.points[23], player)
}

func matches(cell, player Player) uint8 {
	if cell == player {
		return 1
	}
	return 0
}

//golean:verify unprotectedStones : ∀ b player,
//golean:verify+   let points := (List.range 24).map UInt8.ofNat
//golean:verify+   hasUnprotected b player = points.any (fun p => decide («Board$At» b p = player) && !inMill b p player)
func hasUnprotected(board Board, player Player) bool {
	return unprotected(board, 0, player) ||
		unprotected(board, 1, player) ||
		unprotected(board, 2, player) ||
		unprotected(board, 3, player) ||
		unprotected(board, 4, player) ||
		unprotected(board, 5, player) ||
		unprotected(board, 6, player) ||
		unprotected(board, 7, player) ||
		unprotected(board, 8, player) ||
		unprotected(board, 9, player) ||
		unprotected(board, 10, player) ||
		unprotected(board, 11, player) ||
		unprotected(board, 12, player) ||
		unprotected(board, 13, player) ||
		unprotected(board, 14, player) ||
		unprotected(board, 15, player) ||
		unprotected(board, 16, player) ||
		unprotected(board, 17, player) ||
		unprotected(board, 18, player) ||
		unprotected(board, 19, player) ||
		unprotected(board, 20, player) ||
		unprotected(board, 21, player) ||
		unprotected(board, 22, player) ||
		unprotected(board, 23, player)
}

func unprotected(board Board, point Point, player Player) bool {
	return board.At(point) == player && !inMill(board, point, player)
}

//golean:verify slideAvailability : ∀ b player,
//golean:verify+   let points := (List.range 24).map UInt8.ofNat
//golean:verify+   hasSlide b player = points.any (fun f => decide («Board$At» b f = player) &&
//golean:verify+     points.any (fun t => decide («Board$At» b t = 0) && adjacent f t))
func hasSlide(board Board, player Player) bool {
	return hasSlideFrom(board, 0, player) ||
		hasSlideFrom(board, 1, player) ||
		hasSlideFrom(board, 2, player) ||
		hasSlideFrom(board, 3, player) ||
		hasSlideFrom(board, 4, player) ||
		hasSlideFrom(board, 5, player) ||
		hasSlideFrom(board, 6, player) ||
		hasSlideFrom(board, 7, player) ||
		hasSlideFrom(board, 8, player) ||
		hasSlideFrom(board, 9, player) ||
		hasSlideFrom(board, 10, player) ||
		hasSlideFrom(board, 11, player) ||
		hasSlideFrom(board, 12, player) ||
		hasSlideFrom(board, 13, player) ||
		hasSlideFrom(board, 14, player) ||
		hasSlideFrom(board, 15, player) ||
		hasSlideFrom(board, 16, player) ||
		hasSlideFrom(board, 17, player) ||
		hasSlideFrom(board, 18, player) ||
		hasSlideFrom(board, 19, player) ||
		hasSlideFrom(board, 20, player) ||
		hasSlideFrom(board, 21, player) ||
		hasSlideFrom(board, 22, player) ||
		hasSlideFrom(board, 23, player)
}

func hasSlideFrom(board Board, point Point, player Player) bool {
	return board.At(point) == player && hasExit(board, point)
}

func hasExit(board Board, point Point) bool {
	switch point {
	case 0:
		return board.points[7] == Empty || board.points[1] == Empty
	case 1:
		return board.points[0] == Empty || board.points[2] == Empty || board.points[9] == Empty
	case 2:
		return board.points[1] == Empty || board.points[3] == Empty
	case 3:
		return board.points[2] == Empty || board.points[4] == Empty || board.points[11] == Empty
	case 4:
		return board.points[3] == Empty || board.points[5] == Empty
	case 5:
		return board.points[4] == Empty || board.points[6] == Empty || board.points[13] == Empty
	case 6:
		return board.points[5] == Empty || board.points[7] == Empty
	case 7:
		return board.points[6] == Empty || board.points[0] == Empty || board.points[15] == Empty
	case 8:
		return board.points[15] == Empty || board.points[9] == Empty
	case 9:
		return board.points[8] == Empty || board.points[10] == Empty || board.points[1] == Empty || board.points[17] == Empty
	case 10:
		return board.points[9] == Empty || board.points[11] == Empty
	case 11:
		return board.points[10] == Empty || board.points[12] == Empty || board.points[3] == Empty || board.points[19] == Empty
	case 12:
		return board.points[11] == Empty || board.points[13] == Empty
	case 13:
		return board.points[12] == Empty || board.points[14] == Empty || board.points[5] == Empty || board.points[21] == Empty
	case 14:
		return board.points[13] == Empty || board.points[15] == Empty
	case 15:
		return board.points[14] == Empty || board.points[8] == Empty || board.points[7] == Empty || board.points[23] == Empty
	case 16:
		return board.points[23] == Empty || board.points[17] == Empty
	case 17:
		return board.points[16] == Empty || board.points[18] == Empty || board.points[9] == Empty
	case 18:
		return board.points[17] == Empty || board.points[19] == Empty
	case 19:
		return board.points[18] == Empty || board.points[20] == Empty || board.points[11] == Empty
	case 20:
		return board.points[19] == Empty || board.points[21] == Empty
	case 21:
		return board.points[20] == Empty || board.points[22] == Empty || board.points[13] == Empty
	case 22:
		return board.points[21] == Empty || board.points[23] == Empty
	case 23:
		return board.points[22] == Empty || board.points[16] == Empty || board.points[15] == Empty
	default:
		return false
	}
}
