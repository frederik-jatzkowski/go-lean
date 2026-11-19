import movement_arrival.movement_arrival_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/movement_arrival».movement_arrival

private def routes (movement : Movement) : List Step :=
  movement.«field:route».getD []

private def advance (movement : Movement) (step : Step) : Movement :=
  { movement with
    «field:tileID» := step.«field:TileID»
    «field:nextStep» := movement.«field:nextStep» + 1 }

private def clear (movement : Movement) : Movement :=
  { movement with «field:route» := none, «field:nextStep» := 0 }

-- This specification describes the first stopping step and the entire prefix
-- before it. The query history is returned in the order Go calls canEnter.
private def arrival (day : UInt64) (canEnter : Nat → Int64 → Bool) :
    Nat → Movement → List Int64 → Option (Option Movement × Bool × List Int64)
  | 0, _, _ => none
  | fuel + 1, movement, queries =>
    if movement.«field:nextStep» < Int64.ofNat (routes movement).length then
      if movement.«field:nextStep».toInt < 0 then none else
        match (routes movement)[movement.«field:nextStep».toNatClampNeg]? with
        | none => none
        | some step =>
          if day < step.«field:ArrivalDayPassed» then
            some (some movement, false, queries)
          else if step.«field:TileID» = movement.«field:tileID» then
            arrival day canEnter fuel (advance movement step) queries
          else
            let tile := step.«field:TileID»
            let answers := queries ++ [tile]
            if canEnter queries.length tile then
              arrival day canEnter fuel (advance movement step) answers
            else
              some (some (clear movement), true, answers)
    else some (some movement, false, queries)

private theorem loopMatchesArrival (day : UInt64) (canEnter : Nat → Int64 → Bool)
    (fuel : Nat) (movement : Movement) (trace : List Int64) :
    «Movement$Arrive$loop» (some movement) day canEnter fuel trace =
      arrival day canEnter fuel movement trace.reverse := by
  induction fuel generalizing movement trace with
  | zero => rfl
  | succ fuel ih =>
    by_cases guard : movement.«field:nextStep» < Int64.ofNat (movement.«field:route».getD []).length
    · by_cases negative : movement.«field:nextStep».toInt < 0
      · simp [«Movement$Arrive$loop», arrival, routes, guard, negative, bind, Option.bind, Option.map]
      · cases index : (movement.«field:route».getD [])[movement.«field:nextStep».toNatClampNeg]? with
        | none =>
          simp [«Movement$Arrive$loop», arrival, routes, guard, negative, index, bind, Option.bind, Option.map]
        | some step =>
          by_cases future : day < step.«field:ArrivalDayPassed»
          · simp [«Movement$Arrive$loop», arrival, routes, guard, negative, index, future, bind, Option.bind, Option.map]
          · by_cases same : step.«field:TileID» = movement.«field:tileID»
            · simp [«Movement$Arrive$loop», arrival, routes, guard, negative, index, future, same,
                bind, Option.bind, Option.map, ih, advance]
            · cases answer : canEnter trace.length step.«field:TileID» <;>
                simp [«Movement$Arrive$loop», arrival, routes, guard, negative, index, future, same, answer,
                  bind, Option.bind, Option.map, ih, advance, clear, «Movement$PlanRoute»]
    · simp [«Movement$Arrive$loop», arrival, routes, guard, bind, Option.bind, Option.map]

private theorem entryFuel (movement : Movement) (day : UInt64) (canEnter : Nat → Int64 → Bool) :
    «Movement$Arrive» (some movement) day canEnter =
      «Movement$Arrive$loop» (some movement) day canEnter
        (((Int64.ofNat (movement.«field:route».getD []).length).toInt -
          movement.«field:nextStep».toInt).toNat + 1) [] := by rfl

theorem arrivalMatchesSpecification (movement : Movement) (day : UInt64)
    (canEnter : Nat → Int64 → Bool) :
    «Movement$Arrive» (some movement) day canEnter =
      arrival day canEnter
        (((Int64.ofNat (movement.«field:route».getD []).length).toInt -
          movement.«field:nextStep».toInt).toNat + 1)
        movement [] := by
  rw [entryFuel, loopMatchesArrival]
  simp only [List.reverse_nil]

theorem nilReceiverPanics (day : UInt64) (canEnter : Nat → Int64 → Bool) :
    «Movement$Arrive» none day canEnter = none := by rfl

theorem negativeIndexPanics :
    «Movement$Arrive» (some ⟨1, some [⟨2, 0⟩], -1⟩) 0 (fun _ _ => true) = none := by
  rfl

theorem nilAndEmptyRoutesArePreserved (canEnter : Nat → Int64 → Bool) :
    «Movement$Arrive» (some ⟨1, none, 0⟩) 0 canEnter = some (some ⟨1, none, 0⟩, false, []) ∧
    «Movement$Arrive» (some ⟨1, some [], 0⟩) 0 canEnter = some (some ⟨1, some [], 0⟩, false, []) := by
  exact ⟨rfl, rfl⟩

theorem stopsAtFirstFutureStep :
    let route : List Step := [⟨1, 0⟩, ⟨2, 1⟩, ⟨3, 2⟩]
    «Movement$Arrive» (some ⟨1, some route, 0⟩) 1 (fun _ _ => true) =
      some (some ⟨2, some route, 2⟩, false, [2]) := by rfl

theorem obstructionAfterProgressClearsTheRoute :
    «Movement$Arrive» (some ⟨2, some [⟨1, 0⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨4, 1⟩], 1⟩) 1
      (fun query _ => query < 2) = some (some ⟨5, none, 0⟩, true, [4, 5, 4]) := by
  rfl
