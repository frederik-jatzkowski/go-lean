import nine_mens_morris.morris_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/nine_mens_morris».morris.Proofs

theorem startRules : Laws.startRules := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro p
  simp [Start, «Board$At»]

theorem boardSnapshot : Laws.boardSnapshot := by
  intro s
  rfl

theorem currentTurn : Laws.currentTurn := by
  intro s
  rfl

theorem pendingCapture : Laws.pendingCapture := by
  intro s
  rfl

theorem placementPhase : Laws.placementPhase := by
  intro s
  simp [«Game$Placing»]

theorem outsideBoardIsEmpty : Laws.outsideBoardIsEmpty := by
  intro b p outside
  have different : ∀ n : UInt8, n < 24 → p ≠ n := by
    intro n h equal
    subst p
    simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] at *
    omega
  simp [«Board$At», different 0 (by decide), different 1 (by decide), different 2 (by decide),
    different 3 (by decide), different 4 (by decide), different 5 (by decide),
    different 6 (by decide), different 7 (by decide), different 8 (by decide),
    different 9 (by decide), different 10 (by decide), different 11 (by decide),
    different 12 (by decide), different 13 (by decide), different 14 (by decide),
    different 15 (by decide), different 16 (by decide), different 17 (by decide),
    different 18 (by decide), different 19 (by decide), different 20 (by decide),
    different 21 (by decide), different 22 (by decide), different 23 (by decide)]

theorem movementAvailability : Laws.movementAvailability := by
  intro b player
  unfold hasMove
  have ordering : ∀ n : UInt8, n < 3 ∨ n = 3 ∨ 3 < n := by
    intro n
    simp only [UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj]
    omega
  by_cases less : count b player < 3
  · have different : count b player ≠ 3 := by
      intro equal
      rw [equal] at less
      contradiction
    have greater : ¬ 3 < count b player := by
      simpa using UInt8.le_of_lt less
    simp [less, different, greater]
  · by_cases equal : count b player = 3
    · simp [equal]
    · have greater := ((ordering (count b player)).resolve_left less).resolve_left equal
      simp [less, equal, greater]

theorem outcomeRules : Laws.outcomeRules := by
  intro s
  by_cases pending : s.«field:pending» = true <;>
    by_cases rw : s.«field:whiteReserve» = 0 <;>
    by_cases rb : s.«field:blackReserve» = 0 <;>
    by_cases can : hasMove s.«field:board» s.«field:turn» = false <;>
    by_cases white : s.«field:turn» = 1 <;>
    simp_all [«Game$Outcome», «Game$Placing», winner, opponent]

private theorem ongoingAfterOpening (s : Game)
    (pending : s.«field:pending» = false) (rw : s.«field:whiteReserve» = 0)
    (rb : s.«field:blackReserve» = 0) :
    «Game$Outcome» s = 0 ↔ hasMove s.«field:board» s.«field:turn» = true ∧ s.«field:quiet» < 50 := by
  rw [show «Game$Outcome» s = _ from outcomeRules s]
  by_cases can : hasMove s.«field:board» s.«field:turn» = true <;>
    by_cases white : s.«field:turn» = 1 <;>
    by_cases quiet : 50 ≤ s.«field:quiet» <;>
    simp_all [UInt8.not_lt.mpr, UInt8.not_le.mp]

theorem placementLegality : Laws.placementLegality := by
  intro s p
  unfold «Game$CanPlace» «Game$reserve»
  by_cases white : s.«field:turn» = 1 <;>
    by_cases pending : s.«field:pending» = true <;> simp [white, pending]

theorem movementLegality : Laws.movementLegality := by
  intro s f t
  unfold «Game$CanMove» «Game$Placing»
  by_cases pending : s.«field:pending» = false <;>
    by_cases rw : s.«field:whiteReserve» = 0 <;>
    by_cases rb : s.«field:blackReserve» = 0 <;>
    simp [pending, rw, rb]
  rw [ongoingAfterOpening s pending rw rb]
  constructor <;> intro h
  · exact ⟨h.1.2, h.1.1, h.2⟩
  · exact ⟨⟨h.2.1, h.1⟩, h.2.2⟩

theorem captureLegality : Laws.captureLegality := by
  intro s p
  unfold «Game$CanCapture» opponent
  split <;> simp_all
  all_goals split <;> simp_all
  all_goals split <;> simp_all
  all_goals split <;> simp_all

theorem finishingTurn : Laws.finishingTurn := by
  intro s p
  unfold «Game$finishAction» opponent
  split <;> simp_all
  all_goals split <;> simp_all

theorem placeTransition : Laws.placeTransition := by
  intro s p
  unfold «Game$Place»
  split <;> simp_all
  split <;> simp_all

theorem moveTransition : Laws.moveTransition := by
  intro s f t
  simp [«Game$Move»]

theorem captureTransition : Laws.captureTransition := by
  intro s p
  simp [«Game$Capture», opponent]

private theorem pointCases (p : UInt8) (valid : p < 24) :
    p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨ p = 17 ∨ p = 18 ∨ p = 19 ∨ p = 20 ∨ p = 21 ∨ p = 22 ∨ p = 23 := by
  simp only [UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
  omega

set_option maxHeartbeats 3000000 in
theorem boardUpdate : Laws.boardUpdate := by
  intro b p q player validP validQ
  rcases pointCases p validP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases pointCases q validQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem acceptedMove (s : Game) (f t : UInt8)
    (accepted : («Game$Move» s f t).2 = true) :
    «Game$CanMove» s f t = true ∧
      («Game$Move» s f t).1 =
        «Game$finishAction»
          {s with
            «field:board» := setPoint (setPoint s.«field:board» f 0) t s.«field:turn»
            «field:quiet» := s.«field:quiet» + 1} t := by
  by_cases legal : «Game$CanMove» s f t = true
  · exact ⟨legal, by rw [show «Game$Move» s f t = _ from moveTransition s f t]; simp [legal]⟩
  · rw [show «Game$Move» s f t = _ from moveTransition s f t] at accepted
    simp [legal] at accepted

private theorem finishedBoard (s : Game) (t : UInt8) :
    («Game$finishAction» s t).«field:board» = s.«field:board» := by
  rw [show «Game$finishAction» s t = _ from finishingTurn s t]
  split <;> simp_all
  all_goals split <;> rfl

theorem movePreservesOpposingStones : Laws.movePreservesOpposingStones := by
  intro s f t p player accepted hp stone
  obtain ⟨legal, result⟩ := acceptedMove s f t accepted
  obtain ⟨_, _, _, _, _, hf, ht, source, target, _⟩ := (movementLegality s f t).mp legal
  change «Board$At» s.«field:board» p = opponent s.«field:turn» at stone
  have opponentsDiffer : s.«field:turn» ≠ opponent s.«field:turn» := by
    rcases player with color | color <;> simp [opponent, color]
  have opponentNotEmpty : (0 : UInt8) ≠ opponent s.«field:turn» := by
    rcases player with color | color <;> simp [opponent, color]
  have sourceDifferent : p ≠ f := by
    intro eq
    exact opponentsDiffer (source.symm.trans (eq ▸ stone))
  have targetDifferent : p ≠ t := by
    intro eq
    exact opponentNotEmpty (target.symm.trans (eq ▸ stone))
  change «Board$At» («Game$Move» s f t).1.«field:board» p = opponent s.«field:turn»
  rw [result, finishedBoard]
  rw [boardUpdate _ t p _ ht hp, ite_eq_right targetDifferent,
    boardUpdate _ f p _ hf hp, ite_eq_right sourceDifferent]
  exact stone

theorem moveGrantsCaptureExactlyOnMill : Laws.moveGrantsCaptureExactlyOnMill := by
  intro s f t accepted
  obtain ⟨legal, result⟩ := acceptedMove s f t accepted
  have pending := ((movementLegality s f t).mp legal).1
  dsimp only
  rw [result]
  simp only [«Game$Pending», «Game$Board», finishedBoard]
  rw [show «Game$finishAction» _ t = _ from finishingTurn _ t]
  split <;> simp_all [opponent]
  all_goals split <;> simp_all

set_option maxRecDepth 2000 in
set_option maxHeartbeats 3000000 in
theorem boardEdges : Laws.boardEdges := by
  unfold Laws.boardEdges
  decide

set_option maxHeartbeats 3000000 in
theorem millGeometry : Laws.millGeometry := by
  intro board p player valid nonempty
  rcases pointCases p valid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [inMill, «Board$At», nonempty] <;> apply Bool.eq_iff_iff.mpr <;> grind

private def points : List UInt8 := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

set_option maxHeartbeats 3000000 in
theorem countedStones : Laws.countedStones := by
  intro b player
  change count b player = (points.map (fun p => if «Board$At» b p = player then 1 else 0)).foldl (· + ·) 0
  simp [count, «matches», points, «Board$At»]

theorem unprotectedStones : Laws.unprotectedStones := by
  intro b player
  change hasUnprotected b player = points.any (fun p => decide («Board$At» b p = player) && !inMill b p player)
  simp [hasUnprotected, unprotected, points]

private def adjacentVacancy (b : Board) (f : UInt8) : Bool :=
  points.any (fun t => decide («Board$At» b t = 0) && adjacent f t)

set_option maxHeartbeats 5000000 in
private theorem exitAvailability (b : Board) (f : UInt8) (valid : f < 24) :
    hasExit b f = adjacentVacancy b f := by
  rcases pointCases f valid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hasExit, adjacentVacancy, points, «Board$At», adjacent] <;> apply Bool.eq_iff_iff.mpr <;> grind

set_option maxHeartbeats 3000000 in
theorem slideAvailability : Laws.slideAvailability := by
  intro b player
  change hasSlide b player = points.any (fun f => decide («Board$At» b f = player) && adjacentVacancy b f)
  simp [hasSlide, hasSlideFrom, points, ← exitAvailability]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/nine_mens_morris».morris.Proofs
