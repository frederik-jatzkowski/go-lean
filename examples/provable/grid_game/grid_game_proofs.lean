import grid_game.grid_game

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/grid_game».Proofs

theorem stepBoundedEdge : Laws.stepBoundedEdge := by
  unfold Laws.stepBoundedEdge
  decide

theorem stepLeftWraps : Laws.stepLeftWraps := by
  unfold Laws.stepLeftWraps
  decide

theorem stepRightWraps : Laws.stepRightWraps := by
  unfold Laws.stepRightWraps
  decide

theorem stepUpWraps : Laws.stepUpWraps := by
  unfold Laws.stepUpWraps
  decide

theorem stepDownWraps : Laws.stepDownWraps := by
  unfold Laws.stepDownWraps
  decide

theorem stepOrdinaryWall : Laws.stepOrdinaryWall := by
  unfold Laws.stepOrdinaryWall
  decide

theorem stepHorizontalSeamWall : Laws.stepHorizontalSeamWall := by
  unfold Laws.stepHorizontalSeamWall
  decide

theorem stepVerticalSeamWall : Laws.stepVerticalSeamWall := by
  unfold Laws.stepVerticalSeamWall
  decide

theorem stepUnknownDirection : Laws.stepUnknownDirection := by
  unfold Laws.stepUnknownDirection
  decide

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

private theorem replayAgrees (wrap : Bool) (position : Position) (moves : List UInt8) :
    («fold».list replayMove moves (replayState.mk position wrap)).«field:Position» =
      replay wrap position moves := by
  induction moves generalizing position with
  | nil => rfl
  | cons move moves ih => exact ih (Step position move wrap)

/-- No finite list of directions from the Go start position wins in either board mode. -/
theorem youCantWin : Laws.youCantWin := by
  intro wrap moves
  have h := replaySafe wrap Start moves (startSafe wrap)
  simp only [safe, Bool.and_eq_true, and_assoc] at h
  change Won (Replay moves wrap) = false
  rw [Replay, replayAgrees]
  simpa using h.2.2.2.2

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/grid_game».Proofs
