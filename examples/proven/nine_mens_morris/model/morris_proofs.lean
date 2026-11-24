import nine_mens_morris.morris_rules
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/nine_mens_morris/model».Proofs

theorem startRules : Laws.startRules := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro p
  by_cases h : p < 24
  · have board : Start.«field:board».«field:points» = Array.replicate 24 0 := rfl
    simp [«Board$StoneAt», UInt64.not_le.mpr h, board, Array.getElem?_replicate]
    split <;> rfl
  · simp [«Board$StoneAt», UInt64.not_lt.mp h]

theorem startIsValid : Laws.startIsValid := by
  rfl

theorem validTurn : Laws.validTurn := by
  intro s
  by_cases white : s.«field:turn» = 1 <;> simp [«Game$IsValid», white]

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
  simp [«Board$StoneAt», outside]

theorem movementAvailability : Laws.movementAvailability := by
  intro b player
  unfold «Board$hasMove»
  have ordering : ∀ n : UInt8, n < 3 ∨ n = 3 ∨ 3 < n := by
    intro n
    simp only [UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj]
    omega
  by_cases less : «Board$count» b player < 3
  · have different : «Board$count» b player ≠ 3 := by
      intro equal
      rw [equal] at less
      contradiction
    have greater : ¬ 3 < «Board$count» b player := by
      simpa using UInt8.le_of_lt less
    simp [less, different, greater]
  · by_cases equal : «Board$count» b player = 3
    · simp [equal]
    · have greater := ((ordering («Board$count» b player)).resolve_left less).resolve_left equal
      simp [less, equal, greater]

theorem outcomeRules : Laws.outcomeRules := by
  intro s
  by_cases pending : s.«field:pending» = true <;>
    by_cases rw : s.«field:whiteReserve» = 0 <;>
    by_cases rb : s.«field:blackReserve» = 0 <;>
    by_cases can : «Board$hasMove» s.«field:board» s.«field:turn» = false <;>
    by_cases white : s.«field:turn» = 1 <;>
    simp_all [«Game$Outcome», «Game$Placing», winner, opponent]

private theorem ongoingAfterOpening (s : Game)
    (pending : s.«field:pending» = false) (rw : s.«field:whiteReserve» = 0)
    (rb : s.«field:blackReserve» = 0) :
    «Game$Outcome» s = 0 ↔ «Board$hasMove» s.«field:board» s.«field:turn» = true ∧ s.«field:quiet» < 50 := by
  rw [show «Game$Outcome» s = _ from outcomeRules s]
  by_cases can : «Board$hasMove» s.«field:board» s.«field:turn» = true <;>
    by_cases white : s.«field:turn» = 1 <;>
    by_cases quiet : 50 ≤ s.«field:quiet» <;>
    simp_all [UInt8.not_lt.mpr, UInt8.not_le.mp]

theorem placementLegality : Laws.placementLegality := by
  intro s p
  unfold «Game$CanPlace» «Game$reserve»
  by_cases valid : «Game$IsValid» s = true <;> simp [valid, and_assoc]

theorem movementLegality : Laws.movementLegality := by
  intro s f t
  unfold «Game$CanMove» «Game$Placing»
  by_cases valid : «Game$IsValid» s = true <;> simp [valid]
  by_cases pending : s.«field:pending» = false <;>
    by_cases rw : s.«field:whiteReserve» = 0 <;>
    by_cases rb : s.«field:blackReserve» = 0 <;>
    simp [pending, rw, rb]
  rw [ongoingAfterOpening s pending rw rb]
  simp [and_assoc, and_left_comm]

theorem captureLegality : Laws.captureLegality := by
  intro s p
  unfold «Game$CanCapture» opponent
  by_cases valid : «Game$IsValid» s = true <;> simp [valid, and_assoc]

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
  cases h : «Game$CanMove» s f t <;> simp [«Game$Move», h]

theorem captureTransition : Laws.captureTransition := by
  intro s p
  cases h : «Game$CanCapture» s p <;> simp [«Game$Capture», opponent, h]

private theorem finishPreservesValidity (s : Game) (p : UInt64)
    (valid : «Game$IsValid» s = true) :
    «Game$IsValid» («Game$finishAction» s p) = true := by
  rw [show «Game$finishAction» s p = _ from finishingTurn s p]
  rw [validTurn] at valid
  split <;> dsimp only <;> split <;> rw [validTurn] <;> simp_all

theorem placePreservesValidity : Laws.placePreservesValidity := by
  intro s p valid
  rw [show «Game$Place» s p = _ from placeTransition s p]
  split
  · dsimp only
    split <;> apply finishPreservesValidity <;> exact valid
  · exact valid

theorem movePreservesValidity : Laws.movePreservesValidity := by
  intro s f t valid
  rw [show «Game$Move» s f t = _ from moveTransition s f t]
  split
  · exact finishPreservesValidity _ _ valid
  · exact valid

theorem capturePreservesValidity : Laws.capturePreservesValidity := by
  intro s p valid
  rw [show «Game$Capture» s p = _ from captureTransition s p]
  split
  · rw [validTurn]
    split <;> simp
  · exact valid

private theorem pointCases (p : UInt64) (valid : p < 24) :
    p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨ p = 17 ∨ p = 18 ∨ p = 19 ∨ p = 20 ∨ p = 21 ∨ p = 22 ∨ p = 23 := by
  simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
  omega

theorem boardUpdate : Laws.boardUpdate := by
  intro b p q player validP validQ size
  by_cases same : q = p
  · subst p
    have h := size rfl
    simp [«Board$StoneAt», «Board$setPoint», UInt64.not_le.mpr validQ, validQ, h]
  · have different : p.toNat ≠ q.toNat := fun eq => same (UInt64.toNat_inj.mp eq).symm
    simp [«Board$StoneAt», «Board$setPoint», UInt64.not_le.mpr validQ, validP, same, different]

private theorem acceptedMove (s : Game) (f t : UInt64)
    (accepted : («Game$Move» s f t).«field:accepted» = true) :
    «Game$CanMove» s f t = true ∧
      («Game$Move» s f t).«field:next» =
        «Game$finishAction»
          {s with
            «field:board» := «Board$setPoint» («Board$setPoint» s.«field:board» f 0) t s.«field:turn»
            «field:quiet» := s.«field:quiet» + 1} t := by
  by_cases legal : «Game$CanMove» s f t = true
  · exact ⟨legal, by rw [show «Game$Move» s f t = _ from moveTransition s f t]; simp [legal]⟩
  · rw [show «Game$Move» s f t = _ from moveTransition s f t] at accepted
    simp [legal] at accepted

private theorem finishedBoard (s : Game) (t : UInt64) :
    («Game$finishAction» s t).«field:board» = s.«field:board» := by
  rw [show «Game$finishAction» s t = _ from finishingTurn s t]
  split <;> simp_all
  all_goals split <;> rfl

theorem movePreservesOpposingStones : Laws.movePreservesOpposingStones := by
  intro s f t p player accepted hp stone
  obtain ⟨legal, result⟩ := acceptedMove s f t accepted
  obtain ⟨_, _, _, _, _, _, hf, ht, source, target, _⟩ := (movementLegality s f t).mp legal
  change «Board$StoneAt» s.«field:board» p = opponent s.«field:turn» at stone
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
  change «Board$StoneAt» («Game$Move» s f t).«field:next».«field:board» p = opponent s.«field:turn»
  rw [result, finishedBoard]
  rw [boardUpdate _ t p _ ht hp (fun h => (targetDifferent h.symm).elim), ite_eq_right targetDifferent,
    boardUpdate _ f p _ hf hp (fun h => (sourceDifferent h.symm).elim), ite_eq_right sourceDifferent]
  exact stone

theorem moveGrantsCaptureExactlyOnMill : Laws.moveGrantsCaptureExactlyOnMill := by
  intro s f t accepted
  obtain ⟨legal, result⟩ := acceptedMove s f t accepted
  have notPending := ((movementLegality s f t).mp legal).2.1
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
    simp [«Board$inMill», «Board$StoneAt», nonempty] <;> apply Bool.eq_iff_iff.mpr <;> grind

private def points : List UInt64 := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

set_option maxHeartbeats 3000000 in
private def indices : Nat → UInt64 → List UInt64
  | 0, _ => []
  | n + 1, i => i :: indices n (i + 1)

private theorem scanMatchesAny (predicate : UInt64 → boardScan → Bool) (state : boardScan)
    (n : Nat) (i : UInt64) :
    («fold».countUntil (fun point state => (state, predicate point state)) n i state).2 =
      (indices n i).any (fun point => predicate point state) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases hit : predicate i state <;> simp [«fold».countUntil, indices, hit, ih]

private theorem countMatchesFold (b : Board) (player : UInt8) (total : UInt8) (n : Nat) (i : UInt64) :
    («fold».count countStone n i (stoneCount.mk b player total)).«field:Total» =
      ((indices n i).map (fun p => «matches» («Board$StoneAt» b p) player)).foldl (· + ·) total := by
  induction n generalizing i total with
  | zero => rfl
  | succ n ih =>
    simp only [«fold».count, countStone, indices, List.map_cons, List.foldl_cons]
    exact ih _ _

theorem countedStones : Laws.countedStones := by
  intro b player
  change «Board$count» b player = (points.map (fun p => if «Board$StoneAt» b p = player then 1 else 0)).foldl (· + ·) 0
  rw [«Board$count», countMatchesFold]
  change (points.map (fun p => «matches» («Board$StoneAt» b p) player)).foldl (· + ·) 0 = _
  simp [«matches»]

theorem unprotectedStones : Laws.unprotectedStones := by
  intro b player
  change «Board$hasUnprotected» b player = points.any (fun p => decide («Board$StoneAt» b p = player) && !«Board$inMill» b p player)
  change («fold».countUntil (fun point state => (state,
    «Board$unprotected» state.«field:Board» point state.«field:Player»)) 24 0 (boardScan.mk b player)).2 = _
  rw [scanMatchesAny]
  change points.any _ = _
  simp [«Board$unprotected»]

private def adjacentVacancy (b : Board) (f : UInt64) : Bool :=
  points.any (fun t => decide («Board$StoneAt» b t = 0) && adjacent f t)

set_option maxHeartbeats 5000000 in
private theorem exitAvailability (b : Board) (f : UInt64) (valid : f < 24) :
    «Board$hasExit» b f = adjacentVacancy b f := by
  rcases pointCases f valid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [«Board$hasExit», adjacentVacancy, points, «Board$StoneAt», adjacent] <;> apply Bool.eq_iff_iff.mpr <;> grind

set_option maxHeartbeats 3000000 in
theorem slideAvailability : Laws.slideAvailability := by
  intro b player
  change «Board$hasSlide» b player = points.any (fun f => decide («Board$StoneAt» b f = player) && adjacentVacancy b f)
  change («fold».countUntil (fun point state => (state,
    «Board$hasSlideFrom» state.«field:Board» point state.«field:Player»)) 24 0 (boardScan.mk b player)).2 = _
  rw [scanMatchesAny]
  change points.any _ = _
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  apply exists_congr
  intro p
  constructor <;> rintro ⟨member, yes⟩ <;> refine ⟨member, ?_⟩ <;>
    have valid : p < 24 := of_decide_eq_true
      (List.all_eq_true.mp (by decide : points.all (fun p => decide (p < 24)) = true) p member) <;>
    by_cases owns : «Board$StoneAt» b p = player <;>
      simp [«Board$hasSlideFrom», exitAvailability b p valid, owns] at yes ⊢ <;> exact yes

private theorem cellAgrees (b : Board) (p : UInt64) : «Board$StoneAt» b p = Rules.cell b p := by
  by_cases h : p < 24
  · simp [«Board$StoneAt», Rules.cell, h, UInt64.not_le.mpr h]
  · simp [«Board$StoneAt», Rules.cell, h, UInt64.not_lt.mp h]

private theorem writeAgrees (b : Board) (p : UInt64) (color : UInt8) (h : p < 24) :
    «Board$setPoint» b p color = Rules.write b p color := by
  cases b
  simp [«Board$setPoint», Rules.write, h]

private theorem pointBound {p : UInt64} (h : p ∈ Rules.points) : p < 24 := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h
  have bound := List.mem_range.mp hn
  simpa [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2^64 by omega)] using bound

private theorem anyAgrees {α : Type} (xs : List α) {p q : α → Bool}
    (h : ∀ x ∈ xs, p x = q x) : xs.any p = xs.any q := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor <;> rintro ⟨x, hx, accepted⟩ <;> refine ⟨x, hx, ?_⟩
  · rwa [← h x hx]
  · rwa [h x hx]

private theorem edgeAgrees (f t : UInt64) (hf : f < 24) (ht : t < 24) :
    adjacent f t = Rules.edge f t := by
  simpa [Rules.edge, Nat.mod_eq_of_lt (show f.toNat < 2^64 from f.toNat_lt),
    Nat.mod_eq_of_lt (show t.toNat < 2^64 from t.toNat_lt)] using
    boardEdges ⟨f.toNat, UInt64.lt_iff_toNat_lt.mp hf⟩ ⟨t.toNat, UInt64.lt_iff_toNat_lt.mp ht⟩

private theorem millAgrees (b : Board) (p : UInt64) (color : UInt8) (hp : p < 24) (hc : color ≠ 0) :
    «Board$inMill» b p color = Rules.mill b p color := by
  simpa only [Rules.mill, Rules.lines, ← cellAgrees] using millGeometry b p color hp hc

private theorem tallyAgrees (b : Board) (color : UInt8) : «Board$count» b color = Rules.tally b color := by
  simpa only [Rules.tally, Rules.points, ← cellAgrees] using countedStones b color

private theorem exposedAgrees (b : Board) (color : UInt8) (hc : color ≠ 0) :
    «Board$hasUnprotected» b color = Rules.exposed b color := by
  rw [show «Board$hasUnprotected» b color = _ from unprotectedStones b color]
  unfold Rules.exposed
  apply anyAgrees Rules.points
  intro p hp
  rw [cellAgrees, millAgrees b p color (pointBound hp) hc]

private theorem travelAgrees (b : Board) (color : UInt8) :
    «Board$hasMove» b color = true ↔ Rules.canTravel b color := by
  have slides : «Board$hasSlide» b color = (Rules.points.any fun f => decide (Rules.cell b f = color) &&
      Rules.points.any (fun t => decide (Rules.cell b t = 0) && Rules.edge f t)) := by
    rw [show «Board$hasSlide» b color = _ from slideAvailability b color]
    apply anyAgrees Rules.points
    intro f hf
    rw [cellAgrees]
    congr 1
    apply anyAgrees Rules.points
    intro t ht
    rw [cellAgrees, edgeAgrees f t (pointBound hf) (pointBound ht)]
  rw [show «Board$hasMove» b color = true ↔ _ from movementAvailability b color]
  simp only [Rules.canTravel, tallyAgrees, slides]

private theorem otherNotEmpty (color : UInt8) : Rules.other color ≠ 0 := by
  unfold Rules.other
  split <;> decide

theorem outcomeMatchesRules (s : Game) : «Game$Outcome» s = Rules.outcome s := by
  rw [show «Game$Outcome» s = _ from outcomeRules s]
  have blocked : «Board$hasMove» s.«field:board» s.«field:turn» = false ↔
      ¬ Rules.canTravel s.«field:board» s.«field:turn» := by
    rw [← travelAgrees]
    cases «Board$hasMove» s.«field:board» s.«field:turn» <;> simp
  simp only [Rules.outcome, Rules.opening, Rules.other, blocked]
  split <;> simp_all

def canAct (s : Game) : Rules.Action → Bool
  | .place p => «Game$CanPlace» s p
  | .move f t => «Game$CanMove» s f t
  | .capture p => «Game$CanCapture» s p

theorem legalityMatchesRules (s : Game) (a : Rules.Action) :
    canAct s a = true ↔ Rules.legal s a := by
  cases a with
  | place p =>
    unfold canAct
    rw [show «Game$CanPlace» s p = true ↔ _ from placementLegality s p]
    rw [validTurn, cellAgrees]
    rfl
  | move f t =>
    unfold canAct
    rw [show «Game$CanMove» s f t = true ↔ _ from movementLegality s f t]
    unfold Rules.legal Rules.valid
    by_cases hf : f < 24
    · by_cases ht : t < 24
      · rw [validTurn, travelAgrees, edgeAgrees f t hf ht]
        simp only [cellAgrees, tallyAgrees]
      · simp [ht]
    · simp [hf]
  | capture p =>
    unfold canAct
    rw [show «Game$CanCapture» s p = true ↔ _ from captureLegality s p]
    unfold Rules.legal Rules.valid
    by_cases hp : p < 24
    · change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
      have hc : (if s.«field:turn» = 1 then (2 : UInt8) else 1) ≠ 0 :=
        otherNotEmpty s.«field:turn»
      rw [validTurn, cellAgrees, millAgrees _ p _ hp hc, exposedAgrees _ _ hc]
      rfl
    · simp [hp]

private theorem completeAgrees (s : Game) (p : UInt64) (hp : p < 24) (valid : Rules.valid s) :
    «Game$finishAction» s p = Rules.complete s p := by
  have nonempty : s.«field:turn» ≠ 0 := by
    rcases valid with h | h <;> simp [h]
  rw [show «Game$finishAction» s p = _ from finishingTurn s p]
  simp only [Rules.complete, tallyAgrees, millAgrees _ p _ hp nonempty, Rules.other]
  split <;> simp_all

theorem stepMatchesRules (s : Game) (a : Rules.Action) : act s a = Rules.step s a := by
  have legality := legalityMatchesRules s a
  unfold Rules.step
  cases a with
  | place p =>
    change «Game$Place» s p = _
    rw [show «Game$Place» s p = _ from placeTransition s p]
    change («Game$CanPlace» s p = true ↔ _) at legality
    by_cases h : Rules.legal s (.place p)
    · simp only [ite_eq_left h, ite_eq_left (legality.mpr h)]
      obtain ⟨valid, _, _, hp, _⟩ := h
      simp only [Rules.advance, writeAgrees _ p _ hp]
      split <;> apply congrArg (fun next => ActionResult.mk next true) <;>
        apply completeAgrees <;> assumption
    · simp only [ite_eq_right h, ite_eq_right (fun accepted => h (legality.mp accepted))]
  | move f t =>
    change «Game$Move» s f t = _
    rw [show «Game$Move» s f t = _ from moveTransition s f t]
    change («Game$CanMove» s f t = true ↔ _) at legality
    by_cases h : Rules.legal s (.move f t)
    · simp only [ite_eq_left h, ite_eq_left (legality.mpr h)]
      obtain ⟨valid, _, _, _, _, _, hf, ht, _, _, _⟩ := h
      simp only [Rules.advance, writeAgrees _ f _ hf, writeAgrees _ t _ ht]
      apply congrArg (fun next => ActionResult.mk next true)
      apply completeAgrees <;> assumption
    · simp only [ite_eq_right h, ite_eq_right (fun accepted => h (legality.mp accepted))]
  | capture p =>
    change «Game$Capture» s p = _
    rw [show «Game$Capture» s p = _ from captureTransition s p]
    change («Game$CanCapture» s p = true ↔ _) at legality
    by_cases h : Rules.legal s (.capture p)
    · simp only [ite_eq_left h, ite_eq_left (legality.mpr h)]
      obtain ⟨_, _, hp, _, _⟩ := h
      simp only [Rules.advance, writeAgrees _ p _ hp, Rules.other]
    · simp only [ite_eq_right h, ite_eq_right (fun accepted => h (legality.mp accepted))]

theorem startMatchesRules : Start = Rules.initial := by
  rfl

theorem actionPreservesValidity (s : Game) (a : Rules.Action)
    (valid : «Game$IsValid» s = true) : «Game$IsValid» (act s a).«field:next» = true := by
  cases a with
  | place p => exact placePreservesValidity s p valid
  | move f t => exact movePreservesValidity s f t valid
  | capture p => exact capturePreservesValidity s p valid

theorem reachableIsValid (s : Game) (reachable : Rules.Reachable s) :
    «Game$IsValid» s = true := by
  induction reachable with
  | initial => exact startIsValid
  | @next prev a _ legal ih =>
    have preserves := actionPreservesValidity prev a ih
    simpa [stepMatchesRules, Rules.step, legal] using preserves

theorem morrisCorrect (s : Game) (valid : «Game$IsValid» s = true) :
    «Game$Outcome» s = Rules.outcome s ∧
      ∀ a, (canAct s a = true ↔ Rules.legal s a) ∧
        act s a = Rules.step s a ∧ «Game$IsValid» (act s a).«field:next» = true :=
  ⟨outcomeMatchesRules s, fun a =>
    ⟨legalityMatchesRules s a, stepMatchesRules s a, actionPreservesValidity s a valid⟩⟩

theorem historyMatchesRules (s : Game) (actions : List Rules.Action) :
    Rules.history act «Game$Outcome» s actions =
      Rules.history Rules.step Rules.outcome s actions := by
  induction actions generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [Rules.history, stepMatchesRules, outcomeMatchesRules]
    rw [ih]

theorem fromStartMatchesRules (actions : List Rules.Action) :
    (Start, «Game$Outcome» Start, Rules.history act «Game$Outcome» Start actions) =
      (Rules.initial, Rules.outcome Rules.initial,
        Rules.history Rules.step Rules.outcome Rules.initial actions) := by
  rw [historyMatchesRules, outcomeMatchesRules, startMatchesRules]

run_cmd
  for theoremName in [``morrisCorrect, ``reachableIsValid, ``fromStartMatchesRules] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless [`propext, `Quot.sound, `Classical.choice].contains axiomName do
        throwError "Morris proof {theoremName} depends on unapproved axiom {axiomName}"

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/nine_mens_morris/model».Proofs
