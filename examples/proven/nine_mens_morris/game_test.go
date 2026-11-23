package morris_test

import (
	"reflect"
	"testing"

	morris "github.com/frederik-jatzkowski/go-lean/examples/proven/nine_mens_morris"
)

func TestZeroGameRejectsActions(t *testing.T) {
	game := zeroLike(morris.Start())
	if game.IsValid() || !morris.Start().IsValid() {
		t.Fatal("only the started game should have an initialized turn")
	}
	if game.CanPlace(0) || game.CanMove(0, 1) || game.CanCapture(0) {
		t.Fatal("an uninitialized game should have no legal actions")
	}
	if next, ok := unpack(game.Place(0)); ok || !reflect.DeepEqual(next, game) {
		t.Fatal("placement changed or accepted an uninitialized game")
	}
	if next, ok := unpack(game.Move(0, 1)); ok || !reflect.DeepEqual(next, game) {
		t.Fatal("movement changed or accepted an uninitialized game")
	}
	if next, ok := unpack(game.Capture(0)); ok || !reflect.DeepEqual(next, game) {
		t.Fatal("capture changed or accepted an uninitialized game")
	}
}

func TestPublicGameTransitions(t *testing.T) {
	start := morris.Start()
	game := start
	for _, point := range []uint{0, 8, 1, 9, 2} {
		next, ok := unpack(game.Place(point))
		if !ok || next.Board().At(point) != game.Turn() || game.Board().At(point) != morris.Empty {
			t.Fatalf("placement at %d did not return an independent next game", point)
		}
		game = next
	}
	if !game.Pending() || game.Turn() != morris.White {
		t.Fatal("forming a mill should leave White to capture")
	}
	if next, ok := unpack(game.Capture(0)); ok || !reflect.DeepEqual(next, game) {
		t.Fatal("rejecting a capture must return the original game")
	}
	next, ok := unpack(game.Capture(8))
	if !ok || next.Board().At(8) != morris.Empty || next.Pending() || next.Turn() != morris.Black {
		t.Fatal("capture did not return the expected board and turn")
	}
	if game.Board().At(8) != morris.Black || !game.Pending() || start.Board().At(0) != morris.Empty {
		t.Fatal("later actions changed earlier game values")
	}
}

func zeroLike[T any](T) T {
	var zero T
	return zero
}

func unpack[T any](result interface {
	Next() T
	Accepted() bool
}) (T, bool) {
	return result.Next(), result.Accepted()
}
