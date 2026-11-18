import grid_game.grid_game_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/grid_game».grid_game

namespace GridGame

-- The exterior consists of the in-bounds cells outside the goal room and its walls.
private def safe (wrap : Bool) (position : Position) : Bool :=
  decide (position.«field:X».toNat < 8) &&
  decide (position.«field:Y».toNat < 8) &&
  !(decide (position.«field:X» >= 6) && decide (position.«field:Y» <= 1)) &&
  !IsWall position wrap &&
  !Won position

private theorem startSafe (wrap : Bool) : safe wrap Start = true := by
  cases wrap <;> decide

private def cells : List Nat := List.range 8
private def directions : List UInt8 := [0, 1, 2, 3]

-- Check the translated Go transition for every board cell, cardinal move, and mode.
private theorem boardCases (wrap : Bool) :
    cells.all (fun x => cells.all (fun y => directions.all (fun direction =>
      let position := Position.mk (UInt8.ofNat x) (UInt8.ofNat y)
      !safe wrap position || safe wrap (Step position direction wrap)))) = true := by
  cases wrap <;> decide

private theorem stepSafe (wrap : Bool) (position : Position) (direction : UInt8)
    (h : safe wrap position = true) : safe wrap (Step position direction wrap) = true := by
  by_cases hd : direction ∈ directions
  · obtain ⟨x, y⟩ := position
    have bounds := h
    simp only [safe, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at bounds
    have hx : x.toNat ∈ cells := List.mem_range.mpr bounds.1
    have hy : y.toNat ∈ cells := List.mem_range.mpr bounds.2.1
    have checked := List.all_eq_true.mp (boardCases wrap) x.toNat hx
    have checked := List.all_eq_true.mp checked y.toNat hy
    have checked := List.all_eq_true.mp checked direction hd
    simpa [h] using checked
  · have unknown : direction ≠ 0 ∧ direction ≠ 1 ∧ direction ≠ 2 ∧ direction ≠ 3 := by
      simpa [directions, not_or] using hd
    simpa [Step, unknown.1, unknown.2.1, unknown.2.2.1, unknown.2.2.2] using h

def replay (wrap : Bool) (position : Position) (moves : List UInt8) : Position :=
  moves.foldl (fun position direction => Step position direction wrap) position

private theorem replaySafe (wrap : Bool) (position : Position) (moves : List UInt8)
    (h : safe wrap position = true) : safe wrap (replay wrap position moves) = true := by
  induction moves generalizing position with
  | nil => exact h
  | cons direction moves ih =>
    exact ih (Step position direction wrap) (stepSafe wrap position direction h)

/-- No finite list of directions from the Go start position wins in either board mode. -/
theorem youCantWin (wrap : Bool) (moves : List UInt8) :
    Won (replay wrap Start moves) = false := by
  have h := replaySafe wrap Start moves (startSafe wrap)
  simp only [safe, Bool.and_eq_true, and_assoc] at h
  simpa using h.2.2.2.2

end GridGame
