package grid_game

import (
	"slices"
	"testing"
)

func TestPlay(t *testing.T) {
	for _, test := range []struct {
		name string
		wrap bool
		want []Position
	}{
		{"bounded", false, []Position{Start(), {0, 1}, {0, 1}, {0, 2}}},
		{"wraparound", true, []Position{Start(), Start(), Start(), {1, 2}}},
	} {
		t.Run(test.name, func(t *testing.T) {
			moves := []Direction{Left, Left, Down}
			var shown []Position
			calls := 0
			Play(test.wrap, func() (Direction, bool) {
				index := calls
				calls++
				if index >= len(moves) {
					return Right, false
				}
				return moves[index], true
			}, func(position Position) {
				shown = append(shown, position)
			})
			if calls != len(moves)+1 || !slices.Equal(shown, test.want) {
				t.Errorf("Play called next %d times and showed %v, want %d calls and %v",
					calls, shown, len(moves)+1, test.want)
			}
		})
	}
}
