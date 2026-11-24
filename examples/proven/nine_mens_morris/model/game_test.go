package morris_test

import (
	"reflect"
	"testing"

	morris "github.com/frederik-jatzkowski/go-lean/examples/proven/nine_mens_morris/model"
)

func TestZeroGameRejectsActions(t *testing.T) {
	var game morris.Game
	if game.IsValid() || !morris.Start().IsValid() {
		t.Fatal("only the started game should have an initialized turn")
	}
	if game.CanPlace(0) || game.CanMove(0, 1) || game.CanCapture(0) {
		t.Fatal("an uninitialized game should have no legal actions")
	}
	if result := game.Place(0); result.Accepted() || !reflect.DeepEqual(result.Next(), game) {
		t.Fatal("placement changed or accepted an uninitialized game")
	}
	if result := game.Move(0, 1); result.Accepted() || !reflect.DeepEqual(result.Next(), game) {
		t.Fatal("movement changed or accepted an uninitialized game")
	}
	if result := game.Capture(0); result.Accepted() || !reflect.DeepEqual(result.Next(), game) {
		t.Fatal("capture changed or accepted an uninitialized game")
	}
}

func TestPublicGameTransitions(t *testing.T) {
	start := morris.Start()
	game := start
	for _, point := range []uint{0, 8, 1, 9, 2} {
		result := game.Place(point)
		next := result.Next()
		if !result.Accepted() || next.Board().StoneAt(point) != game.Turn() || game.Board().StoneAt(point) != morris.Empty {
			t.Fatalf("placement at %d did not return an independent next game", point)
		}
		game = next
	}
	if !game.Pending() || game.Turn() != morris.White {
		t.Fatal("forming a mill should leave White to capture")
	}
	if result := game.Capture(0); result.Accepted() || !reflect.DeepEqual(result.Next(), game) {
		t.Fatal("rejecting a capture must return the original game")
	}
	result := game.Capture(8)
	next := result.Next()
	if !result.Accepted() || next.Board().StoneAt(8) != morris.Empty || next.Pending() || next.Turn() != morris.Black {
		t.Fatal("capture did not return the expected board and turn")
	}
	if game.Board().StoneAt(8) != morris.Black || !game.Pending() || start.Board().StoneAt(0) != morris.Empty {
		t.Fatal("later actions changed earlier game values")
	}
}
