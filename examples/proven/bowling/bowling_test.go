package bowling

import (
	"slices"
	"testing"
)

func TestScore(t *testing.T) {
	gutters := make([]int, 18)
	tests := []struct {
		name  string
		rolls []int
		score int
	}{
		{"gutter game", make([]int, 20), 0},
		{"perfect game", slices.Repeat([]int{10}, 12), 300},
		{"all spares", slices.Repeat([]int{5}, 21), 150},
		{"ninth-frame strike", append(make([]int, 16), 10, 7, 3, 5), 35},
		{"ninth-frame spare", append(make([]int, 16), 7, 3, 10, 7, 3), 40},
		{"tenth-frame strike and second-rack spare", append(slices.Clone(gutters), 10, 7, 3), 20},
		{"two tenth-frame strikes", append(slices.Clone(gutters), 10, 10, 7), 27},
		{"tenth-frame spare and strike", append(slices.Clone(gutters), 7, 3, 10), 20},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			game := Start()
			for i, pins := range test.rolls {
				if score, complete := scoreGame(game); score != 0 || complete {
					t.Fatalf("before delivery %d, Score() = (%d, %t)", i+1, score, complete)
				}
				game = roll(t, game, pins)
			}
			if score, complete := scoreGame(game); score != test.score || !complete {
				t.Fatalf("Score() = (%d, %t), want (%d, true)", score, complete, test.score)
			}
			checkRejected(t, game, 0)
		})
	}
}

func TestRejectsIllegalRolls(t *testing.T) {
	var game gameState
	checkRejected(t, game, -1)
	checkRejected(t, game, 11)
	game = roll(t, game, 7)
	checkRejected(t, game, 4)
	game = roll(t, game, 2)
	for range 16 {
		game = roll(t, game, 0)
	}
	game = roll(t, game, 10)
	game = roll(t, game, 7)
	checkRejected(t, game, 4)
	game = roll(t, game, 3)
	if score, complete := scoreGame(game); score != 29 || !complete {
		t.Fatalf("Score() after retry = (%d, %t), want (29, true)", score, complete)
	}
}

func roll(t *testing.T, game gameState, pins int) gameState {
	t.Helper()
	next, accepted := rollGame(game, pins)
	if !accepted {
		t.Fatalf("Roll(%d) was rejected", pins)
	}
	return next
}

func checkRejected(t *testing.T, game gameState, pins int) {
	t.Helper()
	if next, accepted := rollGame(game, pins); accepted || next != game {
		t.Fatalf("Roll(%d) should reject and preserve the game", pins)
	}
}

func scoreGame(game gameState) (int, bool) {
	result := game.Score()
	return int(result.Total()), result.Complete()
}

func rollGame(game gameState, pins int) (gameState, bool) {
	result := game.Roll(int64(pins))
	return result.Game(), result.Accepted()
}
