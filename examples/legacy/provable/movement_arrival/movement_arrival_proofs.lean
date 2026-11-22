import movement_arrival.movement_arrival_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/movement_arrival».movement_arrival.Proofs

private def routes (movement : Movement) : List Step :=
  movement.«field:route».getD []

private def advance (movement : Movement) (step : Step) : Movement :=
  { movement with
    «field:tileID» := step.«field:TileID»
    «field:nextStep» := movement.«field:nextStep» + 1 }

private def clear (movement : Movement) : Movement :=
  { movement with «field:route» := none, «field:nextStep» := 0 }

private abbrev arrival (day : UInt64) (canEnter : Nat → Int64 → Bool) :=
  Laws.arrivalMatchesSpecification.arrival day canEnter routes advance clear

private theorem loopMatchesArrival (day : UInt64) (canEnter : Nat → Int64 → Bool)
    (fuel : Nat) (movement : Movement) (trace : List Int64) :
    «Movement$Arrive$loop» (some movement) day canEnter fuel trace =
      arrival day canEnter fuel movement trace.reverse := by
  induction fuel generalizing movement trace with
  | zero => rfl
  | succ fuel ih =>
    by_cases guard : movement.«field:nextStep» < Int64.ofNat (movement.«field:route».getD []).length
    · by_cases negative : movement.«field:nextStep».toInt < 0
      · simp [«Movement$Arrive$loop», arrival, Laws.arrivalMatchesSpecification.arrival, routes, guard, negative, bind, Option.bind, Option.map]
      · cases index : (movement.«field:route».getD [])[movement.«field:nextStep».toNatClampNeg]? with
        | none =>
          simp [«Movement$Arrive$loop», arrival, Laws.arrivalMatchesSpecification.arrival, routes, guard, negative, index, bind, Option.bind, Option.map]
        | some step =>
          by_cases future : day < step.«field:ArrivalDayPassed»
          · simp [«Movement$Arrive$loop», arrival, Laws.arrivalMatchesSpecification.arrival, routes, guard, negative, index, future, bind, Option.bind, Option.map]
          · by_cases same : step.«field:TileID» = movement.«field:tileID»
            · simp [«Movement$Arrive$loop», arrival, Laws.arrivalMatchesSpecification.arrival, routes, guard, negative, index, future, same,
                bind, Option.bind, Option.map, ih, advance]
            · cases answer : canEnter trace.length step.«field:TileID» <;>
                simp [«Movement$Arrive$loop», arrival, Laws.arrivalMatchesSpecification.arrival, routes, guard, negative, index, future, same, answer,
                  bind, Option.bind, Option.map, ih, advance, clear, «Movement$PlanRoute»]
    · simp [«Movement$Arrive$loop», arrival, Laws.arrivalMatchesSpecification.arrival, routes, guard, bind, Option.bind, Option.map]

private theorem entryFuel (movement : Movement) (day : UInt64) (canEnter : Nat → Int64 → Bool) :
    «Movement$Arrive» (some movement) day canEnter =
      «Movement$Arrive$loop» (some movement) day canEnter
        (((Int64.ofNat (movement.«field:route».getD []).length).toInt -
          movement.«field:nextStep».toInt).toNat + 1) [] := by rfl

theorem arrivalMatchesSpecification : Laws.arrivalMatchesSpecification := by
  intro movement day canEnter
  rw [entryFuel, loopMatchesArrival]
  simp only [List.reverse_nil]
  delta arrival routes advance clear
  rfl

theorem nilReceiverPanics : Laws.nilReceiverPanics := by
  intro day canEnter
  rfl

theorem negativeIndexPanics : Laws.negativeIndexPanics := by
  rfl

theorem nilAndEmptyRoutesArePreserved : Laws.nilAndEmptyRoutesArePreserved := by
  intro canEnter
  exact ⟨rfl, rfl⟩

theorem stopsAtFirstFutureStep : Laws.stopsAtFirstFutureStep := by rfl

theorem obstructionAfterProgressClearsTheRoute : Laws.obstructionAfterProgressClearsTheRoute := by
  rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/movement_arrival».movement_arrival.Proofs
