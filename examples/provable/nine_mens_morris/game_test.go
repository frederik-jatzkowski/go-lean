package morris_test

import (
	"testing"

	morris "github.com/frederik-jatzkowski/go-lean/examples/provable/nine_mens_morris"
)

func TestPublicGameTransitions(t *testing.T) {
	start := morris.Start()
	game := start
	for _, point := range []morris.Point{0, 8, 1, 9, 2} {
		next, ok := game.Place(point)
		if !ok || next.Board().At(point) != game.Turn() || game.Board().At(point) != morris.Empty {
			t.Fatalf("placement at %d did not return an independent next game", point)
		}
		game = next
	}
	if !game.Pending() || game.Turn() != morris.White {
		t.Fatal("forming a mill should leave White to capture")
	}
	if next, ok := game.Capture(0); ok || next != game {
		t.Fatal("rejecting a capture must return the original game")
	}
	next, ok := game.Capture(8)
	if !ok || next.Board().At(8) != morris.Empty || next.Pending() || next.Turn() != morris.Black {
		t.Fatal("capture did not return the expected board and turn")
	}
	if game.Board().At(8) != morris.Black || !game.Pending() || start.Board().At(0) != morris.Empty {
		t.Fatal("later actions changed earlier game values")
	}
}
