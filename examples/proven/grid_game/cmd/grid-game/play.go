package main

import game "github.com/frederik-jatzkowski/go-lean/examples/proven/grid_game"

// Play shows the starting position and the position after each move.
// It stops when next returns false.
func play(wrap bool, next func() (uint8, bool), show func(uint8, uint8)) {
	position := game.Start()
	show(position.X(), position.Y())
	for {
		direction, ok := next()
		if !ok {
			return
		}
		position = game.Step(position, direction, wrap)
		show(position.X(), position.Y())
	}
}
