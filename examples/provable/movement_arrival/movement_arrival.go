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
//golean:verify arrivalMatchesSpecification : ∀ (movement : Movement) (day : UInt64) (canEnter : Nat → Int64 → Bool),
//golean:verify+   let routes (movement : Movement) : List Step :=
//golean:verify+     movement.«field:route».getD []
//golean:verify+   let advance (movement : Movement) (step : Step) : Movement :=
//golean:verify+     { movement with
//golean:verify+       «field:tileID» := step.«field:TileID»
//golean:verify+       «field:nextStep» := movement.«field:nextStep» + 1 }
//golean:verify+   let clear (movement : Movement) : Movement :=
//golean:verify+     { movement with «field:route» := none, «field:nextStep» := 0 }
//golean:verify+   let rec arrival :
//golean:verify+       Nat → Movement → List Int64 → Option (Option Movement × Bool × List Int64)
//golean:verify+     | 0, _, _ => none
//golean:verify+     | fuel + 1, movement, queries =>
//golean:verify+       if movement.«field:nextStep» < Int64.ofNat (routes movement).length then
//golean:verify+         if movement.«field:nextStep».toInt < 0 then none else
//golean:verify+           match (routes movement)[movement.«field:nextStep».toNatClampNeg]? with
//golean:verify+           | none => none
//golean:verify+           | some step =>
//golean:verify+             if day < step.«field:ArrivalDayPassed» then
//golean:verify+               some (some movement, false, queries)
//golean:verify+             else if step.«field:TileID» = movement.«field:tileID» then
//golean:verify+               arrival fuel (advance movement step) queries
//golean:verify+             else
//golean:verify+               let tile := step.«field:TileID»
//golean:verify+               let answers := queries ++ [tile]
//golean:verify+               if canEnter queries.length tile then
//golean:verify+                 arrival fuel (advance movement step) answers
//golean:verify+               else
//golean:verify+                 some (some (clear movement), true, answers)
//golean:verify+       else some (some movement, false, queries)
//golean:verify+   «Movement$Arrive» (some movement) day canEnter =
//golean:verify+     arrival
//golean:verify+       (((Int64.ofNat (movement.«field:route».getD []).length).toInt -
//golean:verify+         movement.«field:nextStep».toInt).toNat + 1)
//golean:verify+       movement []
//golean:verify nilReceiverPanics : ∀ (day : UInt64) (canEnter : Nat → Int64 → Bool),
//golean:verify+   «Movement$Arrive» none day canEnter = none
//golean:verify negativeIndexPanics : «Movement$Arrive» (some ⟨1, some [⟨2, 0⟩], -1⟩) 0 (fun _ _ => true) = none
//golean:verify nilAndEmptyRoutesArePreserved : ∀ (canEnter : Nat → Int64 → Bool),
//golean:verify+   «Movement$Arrive» (some ⟨1, none, 0⟩) 0 canEnter = some (some ⟨1, none, 0⟩, false, []) ∧
//golean:verify+   «Movement$Arrive» (some ⟨1, some [], 0⟩) 0 canEnter = some (some ⟨1, some [], 0⟩, false, [])
//golean:verify stopsAtFirstFutureStep : let route : List Step := [⟨1, 0⟩, ⟨2, 1⟩, ⟨3, 2⟩]
//golean:verify+ «Movement$Arrive» (some ⟨1, some route, 0⟩) 1 (fun _ _ => true) =
//golean:verify+ some (some ⟨2, some route, 2⟩, false, [2])
//golean:verify obstructionAfterProgressClearsTheRoute : «Movement$Arrive» (some ⟨2, some [⟨1, 0⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨4, 1⟩], 1⟩) 1
//golean:verify+ (fun query _ => query < 2) = some (some ⟨5, none, 0⟩, true, [4, 5, 4])
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
