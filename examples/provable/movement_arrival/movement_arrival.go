package movementarrival

import "slices"

type Step struct {
	TileID           int
	ArrivalDayPassed uint64
}

type Movement struct {
	tileID   int
	route    []Step
	nextStep int
}

func (movement *Movement) PlanRoute(route []Step) {
	movement.route = slices.Clone(route)
	movement.nextStep = 0
}

// Arrive processes scheduled steps until one is future-dated or obstructed.
//
//golean:verify
func (movement *Movement) Arrive(day uint64, canEnter func(int) bool) bool {
	for movement.nextStep < len(movement.route) {
		step := movement.route[movement.nextStep]
		if step.ArrivalDayPassed > day {
			return false
		}
		if step.TileID != movement.tileID && !canEnter(step.TileID) {
			movement.PlanRoute(nil)
			return true
		}
		movement.tileID = step.TileID
		movement.nextStep++
	}
	return false
}
