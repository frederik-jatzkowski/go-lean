import bowling.bowling_gen

namespace Bowling.Rules

/-- The remaining deliveries in the current frame. Frame numbers start at zero. -/
inductive Phase where
  | first (frame : Int)
  | second (frame first : Int)
  | afterStrike
  | fill (standing : Int)
  | done
  deriving DecidableEq

def Phase.valid : Phase → Prop
  | .first n => 0 ≤ n ∧ n ≤ 9
  | .second n a => (0 ≤ n ∧ n ≤ 9) ∧ 0 ≤ a ∧ a < 10
  | .fill rack => 0 ≤ rack ∧ rack ≤ 10
  | _ => True

def nextFrame (n : Int) : Phase :=
  if n = 9 then .done else .first (n + 1)

/-- Consume a delivery and report how many following balls count for the frame
it finishes. Fill balls are part of the tenth frame. -/
def delivery (phase : Phase) (pins : Int) : Option (Phase × Nat) :=
  if pins < 0 ∨ 10 < pins then none else
  match phase with
  | .first n =>
    if pins = 10 then
      if n = 9 then some (.afterStrike, 0) else some (nextFrame n, 2)
    else some (.second n pins, 0)
  | .second n a =>
    if a + pins > 10 then none
    else if a + pins = 10 then
      if n = 9 then some (.fill 10, 0) else some (nextFrame n, 1)
    else some (nextFrame n, 0)
  | .afterStrike => some (.fill (if pins = 10 then 10 else 10 - pins), 0)
  | .fill rack => if pins ≤ rack then some (.done, 0) else none
  | .done => none

def bonus (balls : Nat) (following : List Int) : Int :=
  (following.take balls).sum

/-- Score completed games by charging each delivery to its own frame and
looking ahead for the bonus when a regular strike or spare closes a frame. -/
def scoreFrom (phase : Phase) : List Int → Option Int
  | [] => if phase = .done then some 0 else none
  | pins :: rest => do
    let (next, balls) ← delivery phase pins
    let score ← scoreFrom next rest
    pure (pins + bonus balls rest + score)

def initial : Phase := .first 0

def score (deliveries : List Int) : Option Int := scoreFrom initial deliveries

/-- The reference game ignores rejected attempts. -/
def play (phase : Phase) : List Int → List Bool × Phase × List Int
  | [] => ([], phase, [])
  | pins :: rest =>
    match delivery phase pins with
    | none =>
      let (accepted, final, rolls) := play phase rest
      (false :: accepted, final, rolls)
    | some (next, _) =>
      let (accepted, final, rolls) := play next rest
      (true :: accepted, final, pins :: rolls)

end Bowling.Rules

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bowling».bowling

/-- Replay attempted Go deliveries, retaining the final state and all decisions. -/
def run (game : Game) : List Int64 → List Bool × Game
  | [] => ([], game)
  | pins :: rest =>
    let (next, accepted) := «Game$Roll» game pins
    let (decisions, final) := run next rest
    (accepted :: decisions, final)

/-- Encode the reference's optional score as the Go result pair. -/
def answer (score : Option Int) : Int64 × Bool :=
  match score with
  | none => (0, false)
  | some total => (Int64.ofInt total, true)

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bowling».bowling
