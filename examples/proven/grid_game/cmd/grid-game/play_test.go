package main

import (
	game "github.com/frederik-jatzkowski/go-lean/examples/proven/grid_game"
	"slices"
	"testing"
)

type point struct{ x, y uint8 }

func TestPlay(t *testing.T) {
	for _, test := range []struct {
		name string
		wrap bool
		want []point
	}{
		{"bounded", false, []point{{game.Start().X(), game.Start().Y()}, {0, 1}, {0, 1}, {0, 2}}},
		{"wraparound", true, []point{{1, 1}, {1, 1}, {1, 1}, {1, 2}}},
	} {
		t.Run(test.name, func(t *testing.T) {
			moves := []uint8{game.Left, game.Left, game.Down}
			var shown []point
			calls := 0
			play(test.wrap, func() (uint8, bool) {
				index := calls
				calls++
				if index >= len(moves) {
					return game.Right, false
				}
				return moves[index], true
			}, func(x, y uint8) {
				shown = append(shown, point{x, y})
			})
			if calls != len(moves)+1 || !slices.Equal(shown, test.want) {
				t.Errorf("Play called next %d times and showed %v, want %d calls and %v",
					calls, shown, len(moves)+1, test.want)
			}
		})
	}
}
