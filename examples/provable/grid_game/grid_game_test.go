package grid_game

import (
	"slices"
	"testing"
)

func TestStep(t *testing.T) {
	tests := []struct {
		name      string
		start     Position
		direction Direction
		wrap      bool
		want      Position
	}{
		{"bounded edge", Position{0, 3}, Left, false, Position{0, 3}},
		{"left wraps", Position{0, 3}, Left, true, Position{7, 3}},
		{"right wraps", Position{7, 3}, Right, true, Position{0, 3}},
		{"up wraps", Position{1, 0}, Up, true, Position{1, 7}},
		{"down wraps", Position{1, 7}, Down, true, Position{1, 0}},
		{"ordinary wall", Position{4, 1}, Right, false, Position{4, 1}},
		{"horizontal seam wall", Start(), Left, true, Start()},
		{"vertical seam wall", Position{7, 6}, Down, true, Position{7, 6}},
		{"unknown direction", Start(), Direction(255), true, Start()},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := Step(test.start, test.direction, test.wrap); got != test.want {
				t.Errorf("Step returned %v, want %v", got, test.want)
			}
		})
	}
}

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
