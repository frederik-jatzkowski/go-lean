package grid_game

import (
	"slices"
	"testing"

	model "github.com/frederik-jatzkowski/go-lean/examples/proven/grid_game/model"
)

func TestWallLayout(t *testing.T) {
	want := [model.Size]string{
		"S....W..",
		"S....W..",
		"......WW",
		"........",
		"........",
		"........",
		"........",
		"......SS",
	}
	for _, wrap := range []bool{false, true} {
		for y, row := range want {
			for x, cell := range row {
				position := model.Position{X: uint8(x), Y: uint8(y)}
				expected := cell == 'W' || (wrap && cell == 'S')
				if got := model.IsWall(position, wrap); got != expected {
					t.Errorf("model.IsWall(%v, %t) = %t, want %t", position, wrap, got, expected)
				}
			}
		}
		for _, position := range []model.Position{{X: model.Size, Y: 2}, {X: 7, Y: model.Size}} {
			if model.IsWall(position, wrap) {
				t.Errorf("model.IsWall(%v, %t) = true outside the board", position, wrap)
			}
		}
	}
}

func TestPlay(t *testing.T) {
	for _, test := range []struct {
		name string
		wrap bool
		want []model.Position
	}{
		{"bounded", false, []model.Position{model.Start(), {X: 0, Y: 1}, {X: 0, Y: 1}, {X: 0, Y: 2}}},
		{"wraparound", true, []model.Position{model.Start(), model.Start(), model.Start(), {X: 1, Y: 2}}},
	} {
		t.Run(test.name, func(t *testing.T) {
			moves := []model.Direction{model.Left, model.Left, model.Down}
			var shown []model.Position
			calls := 0
			Play(test.wrap, func() (model.Direction, bool) {
				index := calls
				calls++
				if index >= len(moves) {
					return model.Right, false
				}
				return moves[index], true
			}, func(position model.Position) {
				shown = append(shown, position)
			})
			if calls != len(moves)+1 || !slices.Equal(shown, test.want) {
				t.Errorf("Play called next %d times and showed %v, want %d calls and %v",
					calls, shown, len(moves)+1, test.want)
			}
		})
	}
}
