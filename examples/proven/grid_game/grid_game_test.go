package grid_game

import (
	"testing"
)

func TestWallLayout(t *testing.T) {
	want := [Size]string{
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
				position := point{x: uint8(x), y: uint8(y)}
				expected := cell == 'W' || (wrap && cell == 'S')
				if got := IsWall(position, wrap); got != expected {
					t.Errorf("IsWall(%v, %t) = %t, want %t", position, wrap, got, expected)
				}
			}
		}
		for _, position := range []point{{x: Size, y: 2}, {x: 7, y: Size}} {
			if IsWall(position, wrap) {
				t.Errorf("IsWall(%v, %t) = true outside the board", position, wrap)
			}
		}
	}
}
