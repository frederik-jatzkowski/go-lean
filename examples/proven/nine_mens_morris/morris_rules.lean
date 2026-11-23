import nine_mens_morris.morris

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/nine_mens_morris».Rules

-- Share the state representation with the implementation. The rules below
-- use its fields without calling any translated Go operation.
inductive Action where
  | place (to : UInt64)
  | move (source to : UInt64)
  | capture (point : UInt64)

def initial : gameState := ⟨⟨Array.replicate 24 0⟩, 9, 9, 1, false, 0⟩

def valid (s : gameState) : Prop :=
  s.«field:turn» = 1 ∨ s.«field:turn» = 2

def points : List UInt64 := (List.range 24).map UInt64.ofNat

def cell (b : boardState) (p : UInt64) : UInt8 :=
  if p < 24 then b.«field:points»[p.toNat]?.getD 0 else 0

def write (b : boardState) (p : UInt64) (color : UInt8) : boardState :=
  ⟨b.«field:points».setIfInBounds p.toNat color⟩

def edge (f t : UInt64) : Bool :=
  let a := f.toNat
  let b := t.toNat
  decide ((a / 8 = b / 8 ∧ ((a + 1) % 8 = b % 8 ∨ (b + 1) % 8 = a % 8)) ∨
    (a % 8 = b % 8 ∧ a % 2 = 1 ∧ (a / 8 + 1 = b / 8 ∨ b / 8 + 1 = a / 8)))

def lines : List (List UInt64) :=
  [[0,1,2], [2,3,4], [4,5,6], [6,7,0], [8,9,10], [10,11,12],
   [12,13,14], [14,15,8], [16,17,18], [18,19,20], [20,21,22],
   [22,23,16], [1,9,17], [3,11,19], [5,13,21], [7,15,23]]

def mill (b : boardState) (p : UInt64) (color : UInt8) : Bool :=
  lines.any (fun line => line.contains p && line.all (fun q => cell b q == color))

def tally (b : boardState) (color : UInt8) : UInt8 :=
  (points.map (fun p => if cell b p = color then 1 else 0)).foldl (· + ·) 0

def canTravel (b : boardState) (color : UInt8) : Prop :=
  (tally b color = 3 ∧ tally b 0 ≠ 0) ∨
  (3 < tally b color ∧ (points.any fun f => decide (cell b f = color) &&
    points.any (fun t => decide (cell b t = 0) && edge f t)) = true)

instance (b : boardState) (color : UInt8) : Decidable (canTravel b color) :=
  inferInstanceAs (Decidable (_ ∨ _))

def other (color : UInt8) : UInt8 := if color = 1 then 2 else 1

def opening (s : gameState) : Prop :=
  s.«field:whiteReserve» ≠ 0 ∨ s.«field:blackReserve» ≠ 0

instance (s : gameState) : Decidable (opening s) :=
  inferInstanceAs (Decidable (_ ∨ _))

def outcome (s : gameState) : UInt8 :=
  if s.«field:pending» = true ∨ opening s then 0
  else if ¬ canTravel s.«field:board» s.«field:turn» then other s.«field:turn»
  else if 50 ≤ s.«field:quiet» then 3 else 0

def reserve (s : gameState) : UInt8 :=
  if s.«field:turn» = 1 then s.«field:whiteReserve» else s.«field:blackReserve»

def exposed (b : boardState) (color : UInt8) : Bool :=
  points.any (fun p => decide (cell b p = color) && !mill b p color)

def legal (s : gameState) : Action → Prop
  | .place p =>
    valid s ∧ s.«field:pending» = false ∧ reserve s ≠ 0 ∧ p < 24 ∧
      cell s.«field:board» p = 0
  | .move f t =>
    valid s ∧ s.«field:pending» = false ∧ s.«field:whiteReserve» = 0 ∧
      s.«field:blackReserve» = 0 ∧ s.«field:quiet» < 50 ∧
      canTravel s.«field:board» s.«field:turn» ∧ f < 24 ∧ t < 24 ∧
      cell s.«field:board» f = s.«field:turn» ∧ cell s.«field:board» t = 0 ∧
      (tally s.«field:board» s.«field:turn» = 3 ∨ edge f t = true)
  | .capture p =>
    let color := other s.«field:turn»
    valid s ∧ s.«field:pending» = true ∧ p < 24 ∧ cell s.«field:board» p = color ∧
      (mill s.«field:board» p color = false ∨ exposed s.«field:board» color = false)

instance (s : gameState) (a : Action) : Decidable (legal s a) := by
  cases a <;> unfold legal valid <;> infer_instance

def complete (s : gameState) (to : UInt64) : gameState :=
  let color := other s.«field:turn»
  if mill s.«field:board» to s.«field:turn» = true ∧ tally s.«field:board» color ≠ 0
  then {s with «field:pending» := true}
  else {s with «field:turn» := color}

def advance (s : gameState) : Action → gameState
  | .place p =>
    let placed := {s with «field:board» := write s.«field:board» p s.«field:turn»}
    complete (if s.«field:turn» = 1 then
      {placed with «field:whiteReserve» := s.«field:whiteReserve» - 1}
    else {placed with «field:blackReserve» := s.«field:blackReserve» - 1}) p
  | .move f t =>
    complete {s with
      «field:board» := write (write s.«field:board» f 0) t s.«field:turn»
      «field:quiet» := s.«field:quiet» + 1} t
  | .capture p =>
    {s with
      «field:board» := write s.«field:board» p 0
      «field:turn» := other s.«field:turn»
      «field:pending» := false
      «field:quiet» := 0}

def step (s : gameState) (a : Action) : actionOutcome :=
  if legal s a then ⟨advance s a, true⟩ else ⟨s, false⟩

inductive Reachable : gameState → Prop where
  | initial : Reachable Rules.initial
  | next {s a} : Reachable s → legal s a → Reachable (advance s a)

-- Record acceptance, state and outcome
-- after every attempted action, including rejected actions.
def history (act : gameState → Action → actionOutcome) (result : gameState → UInt8)
    (s : gameState) : List Action → List (Bool × gameState × UInt8)
  | [] => []
  | a :: rest =>
    let ⟨next, accepted⟩ := act s a
    (accepted, next, result next) :: history act result next rest

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/nine_mens_morris».Rules

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/nine_mens_morris»

def act (s : gameState) : Rules.Action → actionOutcome
  | .place p => «gameState$place» s p
  | .move f t => «gameState$move» s f t
  | .capture p => «gameState$capture» s p

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/nine_mens_morris»
