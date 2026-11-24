package grid_game

import model "github.com/frederik-jatzkowski/go-lean/examples/proven/grid_game/model"

// Play shows the starting position and the position after each move.
// It stops when next returns false.
func Play(wrap bool, next func() (model.Direction, bool), show func(model.Position)) {
	position := model.Start()
	show(position)
	for {
		direction, ok := next()
		if !ok {
			return
		}
		position = model.Step(position, direction, wrap)
		show(position)
	}
}
