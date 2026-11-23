package morris

import (
	"reflect"
	"testing"
)

func position(white, black []uint) boardState {
	board := emptyBoard()
	for _, p := range white {
		board = board.setPoint(uint(p), White)
	}
	for _, p := range black {
		board = board.setPoint(uint(p), Black)
	}
	return board
}

func TestOpeningEndsAfterBothReserves(t *testing.T) {
	state := Start()
	plays := []uint{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18}
	for i, p := range plays {
		if !state.Placing() {
			t.Fatalf("opening ended before placement %d", i)
		}
		next, ok := unpack(state.Place(p))
		if !ok || next.pending {
			t.Fatalf("placement %d at %d: accepted=%t pending=%t", i, p, ok, next.pending)
		}
		state = next
	}
	if state.Placing() || state.turn != White || state.Outcome() != Ongoing {
		t.Fatalf("expected White to start movement, got %+v", state)
	}
	if next, ok := unpack(state.Place(23)); ok || !reflect.DeepEqual(next, state) {
		t.Fatal("accepted placement after opening or changed the state")
	}
}

func TestDoubleMillGrantsOneCapture(t *testing.T) {
	state := gameState{
		board:        position([]uint{0, 2, 9, 17}, []uint{4, 5, 6, 8}),
		whiteReserve: 5,
		blackReserve: 5,
		turn:         White,
	}
	placed, ok := unpack(state.Place(1))
	if !ok || !placed.pending || placed.turn != White || placed.whiteReserve != 4 {
		t.Fatalf("placing at the double mill did not retain White for capture: %+v", placed)
	}
	if next, ok := unpack(placed.Place(3)); ok || !reflect.DeepEqual(next, placed) {
		t.Fatal("allowed another placement while capture was pending")
	}
	if next, ok := unpack(placed.Capture(4)); ok || !reflect.DeepEqual(next, placed) {
		t.Fatal("allowed capturing a mill stone while an unprotected stone was available")
	}
	captured, ok := unpack(placed.Capture(8))
	if !ok || captured.pending || captured.turn != Black || captured.board.At(8) != Empty {
		t.Fatalf("capturing the unprotected stone did not finish White's turn: %+v", captured)
	}
	if next, ok := unpack(captured.Capture(4)); ok || !reflect.DeepEqual(next, captured) {
		t.Fatal("allowed a second capture from a double mill")
	}
}

func TestOnlyMillStonesMayBeCapturedWhenAllAreProtected(t *testing.T) {
	state := gameState{
		board:   position([]uint{0, 1, 2}, []uint{4, 5, 6}),
		turn:    White,
		pending: true,
		quiet:   50,
	}
	if state.Outcome() != Ongoing {
		t.Fatal("decided the outcome before the required capture")
	}
	next, ok := unpack(state.Capture(5))
	if !ok || next.quiet != 0 || next.Outcome() != WhiteWins {
		t.Fatalf("expected legal capture, clock reset, and White win, got %+v", next)
	}
}

func TestSlidingAndFlying(t *testing.T) {
	board := position([]uint{0, 2, 4, 6}, []uint{8, 10, 12, 14})
	state := gameState{board: board, turn: White}
	if next, ok := unpack(state.Move(0, 23)); ok || !reflect.DeepEqual(next, state) {
		t.Fatal("allowed a four-stone player to fly")
	}
	next, ok := unpack(state.Move(0, 1))
	if !ok || next.board.At(0) != Empty || next.board.At(1) != White || next.turn != Black {
		t.Fatalf("adjacent move failed: %+v", next)
	}
	state.board = board.setPoint(6, Empty)
	next, ok = unpack(state.Move(0, 23))
	if !ok || next.board.At(23) != White || next.board.At(0) != Empty {
		t.Fatalf("three-stone player could not fly: %+v", next)
	}
}

func TestFlyingAcrossOpposingStone(t *testing.T) {
	state := gameState{board: position([]uint{0, 8, 16}, []uint{1, 4, 6}), turn: White}
	next, ok := unpack(state.Move(0, 2))
	want := position([]uint{2, 8, 16}, []uint{1, 4, 6})
	if !ok || !reflect.DeepEqual(next.Board(), want) || next.Pending() || next.Turn() != Black {
		t.Fatalf("expected a flight without capture, got %+v (accepted=%t)", next, ok)
	}
}

func TestFlyingIntoMillGrantsSeparateCapture(t *testing.T) {
	state := gameState{board: position([]uint{0, 4, 6}, []uint{1, 8, 10}), turn: White}
	next, ok := unpack(state.Move(0, 5))
	want := position([]uint{4, 5, 6}, []uint{1, 8, 10})
	if !ok || !reflect.DeepEqual(next.Board(), want) || !next.Pending() || next.Turn() != White {
		t.Fatalf("expected a flight with capture pending, got %+v (accepted=%t)", next, ok)
	}
	captured, ok := unpack(next.Capture(1))
	want = position([]uint{4, 5, 6}, []uint{8, 10})
	if !ok || !reflect.DeepEqual(captured.Board(), want) || captured.Pending() || captured.Turn() != Black {
		t.Fatalf("expected only the chosen stone to be captured, got %+v (accepted=%t)", captured, ok)
	}
}

func TestBlockedLosesBeforeDraw(t *testing.T) {
	state := gameState{
		board: position([]uint{0, 2, 4, 6}, []uint{1, 3, 5, 7}),
		turn:  White,
		quiet: DrawAfter,
	}
	if outcome := state.Outcome(); outcome != BlackWins {
		t.Fatalf("blocked White must lose even at the draw limit, got %v", outcome)
	}
}

func TestQuietMoveDraw(t *testing.T) {
	state := gameState{
		board: position([]uint{0, 2, 4, 6}, []uint{8, 10, 12, 14}),
		turn:  White,
		quiet: DrawAfter - 1,
	}
	next, ok := unpack(state.Move(0, 1))
	if !ok || next.quiet != DrawAfter || next.Outcome() != Draw {
		t.Fatalf("quiet move at the threshold must draw, got %+v", next)
	}
	if unchanged, ok := unpack(next.Move(8, 9)); ok || !reflect.DeepEqual(unchanged, next) {
		t.Fatal("accepted a move after the draw")
	}
}

func unpack[T any](result interface {
	Next() T
	Accepted() bool
}) (T, bool) {
	return result.Next(), result.Accepted()
}
