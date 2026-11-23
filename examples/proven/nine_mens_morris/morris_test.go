package morris

import (
	"reflect"
	"testing"
)

func position(white, black []Point) Board {
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
	plays := []Point{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18}
	for i, p := range plays {
		if !state.Placing() {
			t.Fatalf("opening ended before placement %d", i)
		}
		next, ok := state.Place(p)
		if !ok || next.pending {
			t.Fatalf("placement %d at %d: accepted=%t pending=%t", i, p, ok, next.pending)
		}
		state = next
	}
	if state.Placing() || state.turn != White || state.Outcome() != Ongoing {
		t.Fatalf("expected White to start movement, got %+v", state)
	}
	if next, ok := state.Place(23); ok || !reflect.DeepEqual(next, state) {
		t.Fatal("accepted placement after opening or changed the state")
	}
}

func TestDoubleMillGrantsOneCapture(t *testing.T) {
	state := Game{
		board:        position([]Point{0, 2, 9, 17}, []Point{4, 5, 6, 8}),
		whiteReserve: 5,
		blackReserve: 5,
		turn:         White,
	}
	placed, ok := state.Place(1)
	if !ok || !placed.pending || placed.turn != White || placed.whiteReserve != 4 {
		t.Fatalf("placing at the double mill did not retain White for capture: %+v", placed)
	}
	if next, ok := placed.Place(3); ok || !reflect.DeepEqual(next, placed) {
		t.Fatal("allowed another placement while capture was pending")
	}
	if next, ok := placed.Capture(4); ok || !reflect.DeepEqual(next, placed) {
		t.Fatal("allowed capturing a mill stone while an unprotected stone was available")
	}
	captured, ok := placed.Capture(8)
	if !ok || captured.pending || captured.turn != Black || captured.board.At(8) != Empty {
		t.Fatalf("capturing the unprotected stone did not finish White's turn: %+v", captured)
	}
	if next, ok := captured.Capture(4); ok || !reflect.DeepEqual(next, captured) {
		t.Fatal("allowed a second capture from a double mill")
	}
}

func TestOnlyMillStonesMayBeCapturedWhenAllAreProtected(t *testing.T) {
	state := Game{
		board:   position([]Point{0, 1, 2}, []Point{4, 5, 6}),
		turn:    White,
		pending: true,
		quiet:   50,
	}
	if state.Outcome() != Ongoing {
		t.Fatal("decided the outcome before the required capture")
	}
	next, ok := state.Capture(5)
	if !ok || next.quiet != 0 || next.Outcome() != WhiteWins {
		t.Fatalf("expected legal capture, clock reset, and White win, got %+v", next)
	}
}

func TestSlidingAndFlying(t *testing.T) {
	board := position([]Point{0, 2, 4, 6}, []Point{8, 10, 12, 14})
	state := Game{board: board, turn: White}
	if next, ok := state.Move(0, 23); ok || !reflect.DeepEqual(next, state) {
		t.Fatal("allowed a four-stone player to fly")
	}
	next, ok := state.Move(0, 1)
	if !ok || next.board.At(0) != Empty || next.board.At(1) != White || next.turn != Black {
		t.Fatalf("adjacent move failed: %+v", next)
	}
	state.board = board.setPoint(6, Empty)
	next, ok = state.Move(0, 23)
	if !ok || next.board.At(23) != White || next.board.At(0) != Empty {
		t.Fatalf("three-stone player could not fly: %+v", next)
	}
}

func TestFlyingAcrossOpposingStone(t *testing.T) {
	state := Game{board: position([]Point{0, 8, 16}, []Point{1, 4, 6}), turn: White}
	next, ok := state.Move(0, 2)
	want := position([]Point{2, 8, 16}, []Point{1, 4, 6})
	if !ok || !reflect.DeepEqual(next.Board(), want) || next.Pending() || next.Turn() != Black {
		t.Fatalf("expected a flight without capture, got %+v (accepted=%t)", next, ok)
	}
}

func TestFlyingIntoMillGrantsSeparateCapture(t *testing.T) {
	state := Game{board: position([]Point{0, 4, 6}, []Point{1, 8, 10}), turn: White}
	next, ok := state.Move(0, 5)
	want := position([]Point{4, 5, 6}, []Point{1, 8, 10})
	if !ok || !reflect.DeepEqual(next.Board(), want) || !next.Pending() || next.Turn() != White {
		t.Fatalf("expected a flight with capture pending, got %+v (accepted=%t)", next, ok)
	}
	captured, ok := next.Capture(1)
	want = position([]Point{4, 5, 6}, []Point{8, 10})
	if !ok || !reflect.DeepEqual(captured.Board(), want) || captured.Pending() || captured.Turn() != Black {
		t.Fatalf("expected only the chosen stone to be captured, got %+v (accepted=%t)", captured, ok)
	}
}

func TestBlockedLosesBeforeDraw(t *testing.T) {
	state := Game{
		board: position([]Point{0, 2, 4, 6}, []Point{1, 3, 5, 7}),
		turn:  White,
		quiet: DrawAfter,
	}
	if outcome := state.Outcome(); outcome != BlackWins {
		t.Fatalf("blocked White must lose even at the draw limit, got %v", outcome)
	}
}

func TestQuietMoveDraw(t *testing.T) {
	state := Game{
		board: position([]Point{0, 2, 4, 6}, []Point{8, 10, 12, 14}),
		turn:  White,
		quiet: DrawAfter - 1,
	}
	next, ok := state.Move(0, 1)
	if !ok || next.quiet != DrawAfter || next.Outcome() != Draw {
		t.Fatalf("quiet move at the threshold must draw, got %+v", next)
	}
	if unchanged, ok := next.Move(8, 9); ok || !reflect.DeepEqual(unchanged, next) {
		t.Fatal("accepted a move after the draw")
	}
}
