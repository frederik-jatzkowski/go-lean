import bowling.bowling
import Lean.Elab.Command
import Lean.Util.CollectAxioms

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/bowling».Proofs

open Bowling.Rules

theorem startEmpty : Laws.startEmpty := rfl

theorem rejectionUnchanged : Laws.rejectionUnchanged := by
  intro s pins rejected
  unfold «gameState$roll» at rejected ⊢
  repeat (split <;> try simp_all [«gameState$record»])

theorem finalScore : Laws.finalScore := by
  intro s
  simp [«gameState$score»]

theorem completedGameIsStable : Laws.completedGameIsStable := by
  intro game total pins complete
  have frame : game.«field:frame» = 10 := by
    by_cases frame : game.«field:frame» = 10
    · exact frame
    · simp [«gameState$score», frame] at complete
  simp [«gameState$roll», frame, complete]

-- Project the named Go results into the pair representation of the public API.
def rollPair (game : gameState) (pins : Int64) : gameState × Bool :=
  let result := «gameState$roll» game pins
  (result.«field:game», result.«field:accepted»)

def scorePair (game : gameState) : Int64 × Bool :=
  let result := «gameState$score» game
  (result.«field:total», result.«field:complete»)

private abbrev run := replay rollPair

private def pack (n stage rack total one two : Int) : gameState :=
  ⟨Int64.ofInt n, Int64.ofInt stage, Int64.ofInt rack,
    Int64.ofInt total, Int64.ofInt one, Int64.ofInt two⟩

/-- Relate the reference phase and pending score credits to a Go game value. -/
def encode (phase : Phase) (total one two : Int) : gameState :=
  match phase with
  | .first n => pack n 0 0 total one two
  | .second n a => pack n 1 (10 - a) total one two
  | .afterStrike => pack 9 2 0 total one two
  | .fill rack => pack 9 3 rack total one two
  | .done => pack 10 0 0 total one two

private def owesNext (balls : Nat) : Int := if balls = 0 then 0 else 1
private def owesSecond (balls : Nat) : Int := if balls = 2 then 1 else 0

-- Move pending credits forward only after applying the current delivery.
private def modelRoll (phase : Phase) (total one two pins : Int) : gameState × Bool :=
  match delivery phase pins with
  | none => (encode phase total one two, false)
  | some (next, balls) =>
    (encode next (total + pins * (1 + one)) (two + owesNext balls) (owesSecond balls), true)

-- Shifting one outstanding second-ball credit leaves at most two on the next ball.
def CreditBounds (one two : Int) : Prop :=
  (0 ≤ one ∧ one ≤ 2) ∧ (0 ≤ two ∧ two ≤ 1)

private theorem advanceCredits {one two : Int} (h : CreditBounds one two) (balls : Nat) :
    CreditBounds (two + owesNext balls) (owesSecond balls) := by
  obtain ⟨_, hlo, hhi⟩ := h
  unfold CreditBounds owesNext owesSecond
  split <;> split <;> omega

private theorem creditWord (p : Int64) {one two : Int} (h : CreditBounds one two) :
    creditedPins p (Int64.ofInt one) = Int64.ofInt (p.toInt * (1 + one)) := by
  obtain ⟨⟨lo, hi⟩, _⟩ := h
  have cases : one = 0 ∨ one = 1 ∨ one = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · simp [creditedPins]
  · have h : p.toInt + p.toInt = p.toInt * 2 := by omega
    simpa [creditedPins] using congrArg Int64.ofInt h
  · have h : p.toInt + p.toInt + p.toInt = p.toInt * 3 := by omega
    simpa [creditedPins] using congrArg Int64.ofInt h

private theorem smallInt (n : Int) (lo : -20 ≤ n) (hi : n ≤ 20) :
    (Int64.ofInt n).toInt = n :=
  Int64.toInt_ofInt_of_le (by omega) (by omega)

set_option linter.unusedSimpArgs false in
theorem rollMatchesRules (phase : Phase) (valid : phase.valid)
    (total one two : Int) (pins : Int64) (credits : CreditBounds one two) :
    rollPair (encode phase total one two) pins =
      modelRoll phase total one two pins.toInt := by
  by_cases neg : pins.toInt < 0
  · cases phase <;> simp [encode, pack, rollPair, «gameState$roll», modelRoll, delivery,
      Int64.lt_iff_toInt_lt, neg]
  have machineNeg : ¬ pins < (0 : Int64) := by simpa [Int64.lt_iff_toInt_lt] using neg
  by_cases high : 10 < pins.toInt
  all_goals
    have tenLt : ((10 : Int64) < pins) ↔ 10 < pins.toInt := by
      simp [Int64.lt_iff_toInt_lt]
    have ltTen : (pins < (10 : Int64)) ↔ pins.toInt < 10 := by
      simp [Int64.lt_iff_toInt_lt]
    have strikeWord : pins.toInt = 10 → pins = (10 : Int64) := fun h => Int64.toInt_inj.mp h
    cases phase with
    | first n =>
      obtain ⟨lo, hi⟩ := valid
      have hn := smallInt n (by omega) (by omega)
      have n9 : Int64.ofInt n = (9 : Int64) ↔ n = 9 := by
        rw [← Int64.toInt_inj, hn]; rfl
      have n10 : Int64.ofInt n ≠ (10 : Int64) := by
        simp only [ne_eq, ← Int64.toInt_inj, hn]; change n ≠ 10; omega
      by_cases hn9 : n = 9 <;> by_cases strike : pins.toInt = 10
      all_goals by_cases below : pins.toInt < 10
      all_goals try (exfalso; omega)
      all_goals try have hWord := strikeWord strike
      all_goals
        simp [encode, pack, rollPair, «gameState$roll», «gameState$rack», «gameState$record», «nextBonus», «secondBonus», creditWord pins credits,
          modelRoll, delivery, nextFrame, owesNext, owesSecond, Int64.ofInt_add,
          Int64.ofInt_sub, machineNeg, neg, tenLt, ltTen, n9, n10, hn9, high, strike, below] <;> simp_all
    | second n a =>
      obtain ⟨⟨lo, hi⟩, alo, ahi⟩ := valid
      have hn := smallInt n (by omega) (by omega)
      have ha := smallInt (10 - a) (by omega) (by omega)
      have n9 : Int64.ofInt n = (9 : Int64) ↔ n = 9 := by
        rw [← Int64.toInt_inj, hn]; rfl
      have n10 : Int64.ofInt n ≠ (10 : Int64) := by
        simp only [ne_eq, ← Int64.toInt_inj, hn]; change n ≠ 10; omega
      have over : Int64.ofInt (10 - a) < pins ↔ 10 < a + pins.toInt := by
        rw [Int64.lt_iff_toInt_lt, ha]; omega
      have spare : pins = Int64.ofInt (10 - a) ↔ a + pins.toInt = 10 := by
        rw [← Int64.toInt_inj, ha]; omega
      have over' : (10 : Int64) - Int64.ofInt a < pins ↔ 10 < a + pins.toInt := by
        simpa using over
      have spare' : pins = (10 : Int64) - Int64.ofInt a ↔ a + pins.toInt = 10 := by
        simpa using spare
      by_cases overRack : 10 < a + pins.toInt
      all_goals
        by_cases hn9 : n = 9 <;> by_cases eqRack : a + pins.toInt = 10 <;>
          simp [encode, pack, rollPair, «gameState$roll», «gameState$rack», «gameState$record», «nextBonus», «secondBonus», creditWord pins credits,
          modelRoll, delivery, nextFrame, owesNext, owesSecond, Int64.ofInt_add,
          machineNeg, neg, n9, n10, hn9, high, over, spare, over', spare', overRack, eqRack]
      all_goals try have pinsEq := spare'.mpr eqRack
      all_goals try simp_all
      all_goals try omega
    | afterStrike =>
      have strikeEq : pins = (10 : Int64) ↔ pins.toInt = 10 := by
        rw [← Int64.toInt_inj]
        rfl
      by_cases strike : pins.toInt = 10
      all_goals by_cases below : pins.toInt < 10
      all_goals try (exfalso; omega)
      all_goals try have hWord := strikeWord strike
      all_goals
        simp [encode, pack, rollPair, «gameState$roll», «gameState$rack», «gameState$record», «nextBonus», «secondBonus», creditWord pins credits, modelRoll, delivery,
          owesNext, owesSecond, Int64.ofInt_add, Int64.ofInt_sub,
          machineNeg, neg, high, strikeEq, strike, tenLt, ltTen, below] <;> simp_all
    | fill rack =>
      obtain ⟨rlo, rhi⟩ := valid
      have hr := smallInt rack (by omega) (by omega)
      have over : Int64.ofInt rack < pins ↔ rack < pins.toInt := by
        rw [Int64.lt_iff_toInt_lt, hr]
      by_cases within : pins.toInt ≤ rack
      all_goals
        simp [encode, pack, rollPair, «gameState$roll», «gameState$rack», «gameState$record», «nextBonus», «secondBonus», creditWord pins credits,
          modelRoll, delivery, owesNext, owesSecond, Int64.ofInt_add,
          machineNeg, neg, high, over, within, show (rack < pins.toInt) ↔ ¬ pins.toInt ≤ rack by omega]
      all_goals omega
    | done => simp [encode, pack, rollPair, «gameState$roll», modelRoll, delivery, neg, high]


private def budget : Phase → Int
  | .first n => 30 * (10 - n)
  | .second n a => 30 * (10 - n) - a
  | .afterStrike => 20
  | .fill rack => rack
  | .done => 0

private theorem deliveryFacts {phase next : Phase} {pins : Int} {balls : Nat}
    (valid : phase.valid) (h : delivery phase pins = some (next, balls)) :
    next.valid ∧ (0 ≤ pins ∧ pins ≤ 10) ∧ balls ≤ 2 ∧
      pins + 10 * (balls : Int) + budget next ≤ budget phase := by
  cases phase <;> simp only [Phase.valid] at valid <;>
    simp only [delivery, nextFrame] at h <;>
    (repeat' split at h) <;> simp at h
  all_goals
    obtain ⟨rfl, rfl⟩ := h
    simp [Phase.valid, budget]
    (repeat' apply And.intro) <;> omega

-- A zero-pin delivery is always possible until the game ends. This measure
-- counts the maximum remaining deliveries for the purpose of that completion.
private def remaining : Phase → Int
  | .first n => 2 * (9 - n) + 3
  | .second n _ => 2 * (9 - n) + 2
  | .afterStrike => 2
  | .fill _ => 1
  | .done => 0

private theorem remainingNonnegative {phase : Phase} (valid : phase.valid) :
    0 ≤ remaining phase := by
  cases phase <;> simp [remaining, Phase.valid] at valid ⊢ <;> omega

private theorem zeroProgress {phase : Phase} (valid : phase.valid) (ongoing : phase ≠ .done) :
    ∃ next balls, delivery phase 0 = some (next, balls) ∧ remaining next < remaining phase := by
  cases phase with
  | first n => exact ⟨.second n 0, 0, by simp [delivery], by simp [remaining]⟩
  | second n a =>
    obtain ⟨_, alo, ahi⟩ := valid
    have noSpare : a ≠ 10 := by omega
    have fits : ¬10 < a := by omega
    refine ⟨nextFrame n, 0, by simp [delivery, noSpare, fits], ?_⟩
    by_cases hn : n = 9 <;> simp [nextFrame, remaining, hn] <;> omega
  | afterStrike => exact ⟨.fill 10, 0, by simp [delivery], by simp [remaining]⟩
  | fill rack =>
    obtain ⟨lo, _⟩ := valid
    exact ⟨.done, 0, by simp [delivery, lo], by simp [remaining]⟩
  | done => exact False.elim (ongoing rfl)

private theorem hasCompletion (phase : Phase) (valid : phase.valid) :
    ∃ rolls total, scoreFrom phase rolls = some total := by
  by_cases done : phase = .done
  · exact ⟨[], 0, by simp [scoreFrom, done]⟩
  obtain ⟨next, balls, step, progress⟩ := zeroProgress valid done
  have nv := (deliveryFacts valid step).1
  obtain ⟨rolls, total, scored⟩ := hasCompletion next nv
  exact ⟨0 :: rolls, bonus balls rolls + total, by simp [scoreFrom, step, scored]⟩
termination_by (remaining phase).toNat
decreasing_by
  have := remainingNonnegative nv
  omega

/-- A delivery is legal exactly when it can begin a legal completion of the
current game. In particular, every accepted prefix can still be completed. -/
theorem legalDeliveryIffCompletable (phase : Phase) (valid : phase.valid) (pins : Int) :
    (∃ next balls, delivery phase pins = some (next, balls)) ↔
      ∃ rest total, scoreFrom phase (pins :: rest) = some total := by
  constructor
  · rintro ⟨next, balls, step⟩
    obtain ⟨rest, total, scored⟩ := hasCompletion next (deliveryFacts valid step).1
    exact ⟨rest, pins + bonus balls rest + total, by simp [scoreFrom, step, scored]⟩
  · rintro ⟨rest, total, scored⟩
    cases step : delivery phase pins with
    | none => simp [scoreFrom, step] at scored
    | some result =>
      obtain ⟨next, balls⟩ := result
      exact ⟨next, balls, rfl⟩

theorem rollAcceptedIffCompletable (phase : Phase) (valid : phase.valid)
    (total one two : Int) (pins : Int64) (credits : CreditBounds one two) :
    (rollPair (encode phase total one two) pins).2 = true ↔
      ∃ rest score, scoreFrom phase (pins.toInt :: rest) = some score := by
  rw [← legalDeliveryIffCompletable phase valid, rollMatchesRules phase valid total one two pins credits]
  cases h : delivery phase pins.toInt with
  | none => simp [modelRoll, h]
  | some result =>
    obtain ⟨next, balls⟩ := result
    simp [modelRoll, h]

private theorem bonusBounds {rolls : List Int}
    (h : ∀ p ∈ rolls, 0 ≤ p ∧ p ≤ 10) (n : Nat) :
    0 ≤ bonus n rolls ∧ bonus n rolls ≤ 10 * (n : Int) := by
  induction n generalizing rolls with
  | zero => simp [bonus]
  | succ n ih =>
    cases rolls with
    | nil => simp [bonus]; omega
    | cons p ps =>
      have hp := h p (by simp)
      have ht := ih (rolls := ps) (fun q hq => h q (by simp [hq]))
      simp [bonus, List.take_succ_cons] at ht ⊢
      omega

private theorem scoreBounds {phase : Phase} {rolls : List Int} {total : Int}
    (valid : phase.valid) (scored : scoreFrom phase rolls = some total) :
    (∀ p ∈ rolls, 0 ≤ p ∧ p ≤ 10) ∧ 0 ≤ total ∧ total ≤ budget phase := by
  induction rolls generalizing phase total with
  | nil =>
    by_cases h : phase = .done <;> simp [scoreFrom, h, budget] at scored ⊢
    omega
  | cons p ps ih =>
    cases hd : delivery phase p with
    | none => simp [scoreFrom, hd] at scored
    | some result =>
      obtain ⟨next, balls⟩ := result
      cases hr : scoreFrom next ps with
      | none => simp [scoreFrom, hd, hr] at scored
      | some score =>
        obtain ⟨nv, pinBounds, _, cost⟩ := deliveryFacts valid hd
        obtain ⟨pinTail, _, _⟩ := ih nv hr
        have hb := bonusBounds pinTail balls
        simp [scoreFrom, hd, hr] at scored
        constructor
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact pinBounds
          · exact pinTail q hq
        · omega

private def pending (one two : Int) (rolls : List Int) : Int :=
  one * rolls[0]?.getD 0 + two * rolls[1]?.getD 0

private theorem shiftPending (p one two : Int) (rolls : List Int) {balls : Nat}
    (h : balls ≤ 2) :
    p * (1 + one) + pending (two + owesNext balls) (owesSecond balls) rolls =
      pending one two (p :: rolls) + p + bonus balls rolls := by
  have choices : balls = 0 ∨ balls = 1 ∨ balls = 2 := by omega
  rcases choices with rfl | rfl | rfl <;>
    cases rolls with
    | nil => simp [pending, bonus, owesNext, owesSecond, Int.mul_add, Int.mul_comm] <;> omega
    | cons q qs =>
      cases qs <;>
        simp [pending, bonus, owesNext, owesSecond, Int.mul_add, Int.mul_comm] <;> omega

private theorem scoreAgrees (phase : Phase) (valid : phase.valid) (total one two : Int) :
    scorePair (encode phase total one two) =
      answer ((scoreFrom phase []).map (fun s => total + s)) := by
  have notDone (n : Int) (lo : 0 ≤ n) (hi : n ≤ 9) : Int64.ofInt n ≠ (10 : Int64) := by
    simp only [ne_eq, ← Int64.toInt_inj, smallInt n (by omega) (by omega)]
    change n ≠ 10
    omega
  cases phase with
  | first n =>
    obtain ⟨lo, hi⟩ := valid
    simp [encode, pack, scorePair, «gameState$score», scoreFrom, answer, notDone n lo hi]
  | second n a =>
    obtain ⟨⟨lo, hi⟩, _⟩ := valid
    simp [encode, pack, scorePair, «gameState$score», scoreFrom, answer, notDone n lo hi]
  | afterStrike | fill | done => simp [encode, pack, scorePair, «gameState$score», scoreFrom, answer]

-- Each pending obligation adds to the score of the accepted suffix. The
-- reference scorer gets the same deliveries by looking ahead from their frame.
private theorem runAgrees (phase : Phase) (valid : phase.valid)
    (total one two : Int) (attempts : List Int64) (credits : CreditBounds one two) :
    let reference := play phase (attempts.map Int64.toInt)
    let actual := run (encode phase total one two) attempts
    actual.1 = reference.1 ∧
      scorePair actual.2 =
        answer ((scoreFrom phase reference.2.2).map
          (fun s => total + pending one two reference.2.2 + s)) := by
  induction attempts generalizing phase total one two with
  | nil =>
    simp [play, replay, pending]
    exact scoreAgrees phase valid total one two
  | cons p ps ih =>
    simp only [List.map_cons, replay, rollMatchesRules phase valid total one two p credits, modelRoll, play]
    cases hd : delivery phase p.toInt with
    | none =>
      simpa [hd] using ih phase valid total one two credits
    | some result =>
      obtain ⟨next, balls⟩ := result
      obtain ⟨nv, _, ballBound, _⟩ := deliveryFacts valid hd
      obtain ⟨decisions, scored⟩ :=
        ih next nv (total + p.toInt * (1 + one)) (two + owesNext balls) (owesSecond balls) (advanceCredits credits balls)
      simp only [List.cons.injEq, true_and]
      refine ⟨decisions, scored.trans ?_⟩
      let rolls := (play next (ps.map Int64.toInt)).2.2
      change answer ((scoreFrom next rolls).map _) = answer ((scoreFrom phase (p.toInt :: rolls)).map _)
      have shift := shiftPending p.toInt one two rolls ballBound
      cases hs : scoreFrom next rolls with
      | none => simp [scoreFrom, hd, hs]
      | some s =>
        have hsum : total + p.toInt * (1 + one) +
            pending (two + owesNext balls) (owesSecond balls) rolls + s =
            total + pending one two (p.toInt :: rolls) + (p.toInt + bonus balls rolls + s) := by omega
        simp [scoreFrom, hd, hs]
        exact congrArg (fun n => answer (some n)) hsum

private theorem collectAttempts (game : gameState) (prior : List Bool) (attempts : List Int64) :
    «fold».list replayAttempt attempts (replayResult.mk game prior) =
      replayResult.mk (run game attempts).2 ((run game attempts).1.reverse ++ prior) := by
  induction attempts generalizing game prior with
  | nil => rfl
  | cons pins attempts ih =>
    change «fold».list replayAttempt attempts
      (replayResult.mk («gameState$roll» game pins).«field:game»
        ((«gameState$roll» game pins).«field:accepted» :: prior)) = _
    rw [ih]
    simp [replay, rollPair, List.append_assoc]

private theorem orderDecisions (pending ordered : List Bool) :
    «fold».list prependDecision pending ordered = pending.reverse ++ ordered := by
  induction pending generalizing ordered with
  | nil => rfl
  | cons decision pending ih =>
    change «fold».list prependDecision pending (decision :: ordered) = _
    rw [ih]
    simp [List.append_assoc]

private theorem replayAgrees (attempts : List Int64) :
    Replay attempts = replayResult.mk (run Start attempts).2 (run Start attempts).1 := by
  simp [Replay, collectAttempts, orderDecisions]

/-- The model agrees on the acceptance of every attempt, and on whether a
final score exists and what it is after any such history. -/
theorem fromStartMatchesRules : Laws.fromStartMatchesRules := by
  intro attempts
  dsimp only
  simp only [replayAgrees]
  have start : Start = encode initial 0 0 0 := rfl
  change (run Start attempts).1 = (play initial (attempts.map Int64.toInt)).1 ∧
    scorePair (run Start attempts).2 = answer (score (play initial (attempts.map Int64.toInt)).2.2)
  rw [start]
  simpa [score, pending] using runAgrees initial (by simp [initial, Phase.valid]) 0 0 0 attempts (by simp [CreditBounds])

/-- The reference score of a completed game fits the Go result without wrap. -/
theorem completedScoreBounds {rolls : List Int} {total : Int} (h : score rolls = some total) :
    0 ≤ total ∧ total ≤ 300 := by
  exact (scoreBounds (phase := initial) (by simp [initial, Phase.valid]) h).2

theorem goScoreBounds (attempts : List Int64) (total : Int64)
    (h : scorePair (run Start attempts).2 = (total, true)) :
    0 ≤ total.toInt ∧ total.toInt ≤ 300 := by
  have scoreEq := (fromStartMatchesRules attempts).2
  rw [replayAgrees] at scoreEq
  change scorePair (run Start attempts).2 =
    answer (score (play initial (attempts.map Int64.toInt)).2.2) at scoreEq
  rw [h] at scoreEq
  cases hr : score (play initial (attempts.map Int64.toInt)).2.2 with
  | none => simp [hr, answer] at scoreEq
  | some s =>
    obtain ⟨lo, hi⟩ := completedScoreBounds hr
    simp [hr, answer] at scoreEq
    rw [scoreEq, Int64.toInt_ofInt_of_le (by omega) (by omega)]
    exact ⟨lo, hi⟩

private def encodeToken : Bowling.Grammar.Token → token
  | .count n => ⟨n, false⟩
  | .comma => ⟨0, true⟩

private def lexResult (r : lexer × Bool) : Option (List token) :=
  if r.2 then none else some (flushOne r.1).«field:tokens»

private theorem byteAtList (data : ByteArray) (i : Nat) :
    data[i]? = data.data.toList[i]? := by
  by_cases h : i < data.size
  · simp [getElem?_pos, h, ByteArray.getElem_eq_getElem_data, ByteArray.size_data]
  · simp [getElem?_neg, h, ByteArray.size_data]

private theorem spellOne (bs : List UInt8) (h : bs.head? ≠ some 48) :
    Bowling.Grammar.spell (49 :: bs) =
      (Bowling.Grammar.spell bs).map (· ++ [.count 1]) := by
  cases bs <;> simp_all [Bowling.Grammar.spell]

private theorem spellTen (bs : List UInt8) :
    Bowling.Grammar.spell (49 :: 48 :: bs) =
      (Bowling.Grammar.spell bs).map (· ++ [.count 10]) := by
  simp [Bowling.Grammar.spell]

private def spelled (pending : Bool) (bs : List UInt8) (ts : List token) :
    Option (List token) :=
  (Bowling.Grammar.spell (if pending then 49 :: bs else bs)).map
    fun more => more.map encodeToken ++ ts

private theorem singleCount (b : UInt8) (bounds : 48 ≤ b ∧ b ≤ 57) :
    digit b = Int64.ofNat (b.toNat - 48) := by
  have limits : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
    simpa [UInt8.le_iff_toNat_le] using bounds
  have choices : b.toNat = 48 ∨ b.toNat = 49 ∨ b.toNat = 50 ∨ b.toNat = 51 ∨
      b.toNat = 52 ∨ b.toNat = 53 ∨ b.toNat = 54 ∨ b.toNat = 55 ∨
      b.toNat = 56 ∨ b.toNat = 57 := by omega
  rcases choices with h | h | h | h | h | h | h | h | h | h <;>
    have eq := congrArg UInt8.ofNat h <;>
    simp at eq <;> subst b <;> rfl

private theorem spellSingle (b : UInt8) (bs : List UInt8) (h : b ≠ 49) :
    Bowling.Grammar.spell (b :: bs) =
      (Bowling.Grammar.single b).bind fun ts => (Bowling.Grammar.spell bs).map (· ++ ts) := by
  rw [Bowling.Grammar.spell.eq_def]
  simp [h]

set_option linter.unusedSimpArgs false in
private theorem scanSingleSpec (b : UInt8) (data : ByteArray) (ts : List token)
    (bs : List UInt8) :
    let r := scanSingle b ⟨data, ts, false⟩
    (if r.2 then none else spelled r.1.«field:pending» bs r.1.«field:tokens») =
      spelled false (b :: bs) ts := by
  by_cases one : b = 49
  · subst b
    simp [scanSingle, spelled]
  by_cases comma : b = 44
  · subst b
    cases h : Bowling.Grammar.spell bs <;>
      simp [scanSingle, spelled, spellSingle, Bowling.Grammar.single, h, encodeToken]
  by_cases ws : b = 32 ∨ b = 9 ∨ b = 13 ∨ b = 10
  · rcases ws with h | h | h | h <;> subst b <;>
      cases h : Bowling.Grammar.spell bs <;>
      simp [scanSingle, spelled, spellSingle, Bowling.Grammar.single, h]
  by_cases lo : 48 ≤ b
  · by_cases hi : b ≤ 57
    · have value := singleCount b ⟨lo, hi⟩
      cases h : Bowling.Grammar.spell bs <;>
        simp [scanSingle, spelled, spellSingle, Bowling.Grammar.single,
          h, one, comma, ws, lo, hi, value, encodeToken]
    · simp [scanSingle, spelled, spellSingle, Bowling.Grammar.single,
        one, comma, ws, lo, hi, or_assoc]
  · simp [scanSingle, spelled, spellSingle, Bowling.Grammar.single,
      one, comma, ws, lo, or_assoc]

private theorem scanByteSpec (i : UInt64) (data : ByteArray) (b : UInt8)
    (atByte : data[i.toNat]? = some b) (ts : List token) (pending : Bool) (bs : List UInt8) :
    let r := lexByte i ⟨data, ts, pending⟩
    (if r.2 then none else spelled r.1.«field:pending» bs r.1.«field:tokens») =
      spelled pending (b :: bs) ts := by
  dsimp only
  cases pending
  · simpa [lexByte, atByte, flushOne] using scanSingleSpec b data ts bs
  · by_cases zero : b = 48
    · subst b
      cases h : Bowling.Grammar.spell bs <;>
        simp [lexByte, atByte, spelled, spellTen, h, encodeToken]
    · rw [show spelled true (b :: bs) ts =
          spelled false (b :: bs) (encodeToken (.count 1) :: ts) by
          simp only [spelled, Bool.false_eq_true, ↓reduceIte, spellOne (b :: bs) (by simpa using zero)]
          cases Bowling.Grammar.spell (b :: bs) <;> simp]
      simp only [lexByte, atByte, Option.getD_some, zero, decide_false,
        Bool.false_eq_true, ↓reduceIte, flushOne, Bool.not_true, encodeToken]
      exact scanSingleSpec b data (⟨1, false⟩ :: ts) bs

private theorem countLex (data : ByteArray) (bs : List UInt8) (i : UInt64)
    (suffix : data.data.toList.drop i.toNat = bs)
    (fits : data.size < UInt64.size) (ts : List token) (pending : Bool) :
    lexResult («fold».countUntil lexByte bs.length i ⟨data, ts, pending⟩) =
      spelled pending bs ts := by
  induction bs generalizing i ts pending with
  | nil => cases pending <;> simp [«fold».countUntil, lexResult, flushOne, spelled,
      Bowling.Grammar.spell, encodeToken]
  | cons b bs ih =>
    have atByte : data[i.toNat]? = some b := by
      rw [byteAtList]
      simpa [List.getElem?_drop] using congrArg List.head? suffix
    have bound : i.toNat < data.size := by
      have := getElem?_eq_some_iff.mp atByte
      exact this.1
    have next : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 by rfl, Nat.mod_eq_of_lt]
      change i.toNat + 1 < UInt64.size
      omega
    have rest : data.data.toList.drop (i + 1).toNat = bs := by
      rw [next, ← List.drop_drop]
      simp [suffix]
    have step := scanByteSpec i data b atByte ts pending bs
    rw [List.length_cons, «fold».countUntil]
    generalize hr : lexByte i ⟨data, ts, pending⟩ = r at step ⊢
    obtain ⟨⟨input, tokens, pending'⟩, stop⟩ := r
    have same : input = data := by
      have hp := congrArg (fun v : lexer × Bool => v.1.«field:input») hr
      have stays (b : UInt8) (state : lexer) :
          (scanSingle b state).1.«field:input» = state.«field:input» := by
        unfold scanSingle
        split <;> try rfl
        split <;> try rfl
        split <;> try rfl
        repeat' first | rfl | split
      simp only [lexByte, atByte, Option.getD_some] at hp
      cases pending <;> by_cases h : b = 48 <;> simpa [h, stays, flushOne] using hp.symm
    subst input
    cases stop
    · simpa [ih _ rest] using step
    · simpa [lexResult] using step

private theorem lexSpec (data : ByteArray) (fits : data.size < UInt64.size) :
    lex data = (Bowling.Grammar.spell data.data.toList).map (List.map encodeToken) := by
  have length : (UInt64.ofNat data.size).toNat = data.data.toList.length := by
    simp [Nat.mod_eq_of_lt fits, ByteArray.size_data]
  change lexResult («fold».countUntil lexByte (UInt64.ofNat data.size).toNat 0 ⟨data, [], false⟩) = _
  rw [length, countLex data _ _ (by simp) fits]
  simp [spelled]

set_option linter.unusedSimpArgs false in
private theorem parseNonempty (t : Bowling.Grammar.Token) (ts : List Bowling.Grammar.Token)
    (acc : List Int64) :
    finishParse («fold».listUntil parseToken ((t :: ts).map encodeToken) ⟨acc, false⟩) =
      (Bowling.Grammar.nonempty (t :: ts)).map (· ++ acc) := by
  cases t with
  | comma => cases ts <;> simp [«fold».listUntil, parseToken, encodeToken, finishParse,
      Bowling.Grammar.nonempty]
  | count n =>
    cases ts with
    | nil => simp [«fold».listUntil, parseToken, encodeToken, finishParse,
        Bowling.Grammar.nonempty]
    | cons next rest =>
      cases next with
      | count m => simp [«fold».listUntil, parseToken, encodeToken, finishParse,
          Bowling.Grammar.nonempty]
      | comma =>
        cases rest with
        | nil => simp [«fold».listUntil, parseToken, encodeToken, finishParse,
            Bowling.Grammar.nonempty]
        | cons t ts =>
          have ih := parseNonempty t ts (n :: acc)
          simp only [List.map_cons, «fold».listUntil, encodeToken, parseToken,
            ne_self_iff_false, ↓reduceIte, Bool.false_eq_true, Bool.not_true,
            Bowling.Grammar.nonempty] at ⊢
          change finishParse («fold».listUntil parseToken ((t :: ts).map encodeToken)
            ⟨n :: acc, false⟩) = _
          rw [ih]
          cases Bowling.Grammar.nonempty (t :: ts) <;> simp
termination_by ts.length

private theorem parseSpec (ts : List Bowling.Grammar.Token) :
    parse (ts.map encodeToken) = Bowling.Grammar.counts ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simpa [parse, Bowling.Grammar.counts] using parseNonempty t ts []

private theorem playGrammar (input : ByteArray) (fits : input.size < UInt64.size) :
    playInput input =
      ((Bowling.Grammar.spell input.data.toList).bind Bowling.Grammar.counts).map Replay := by
  unfold playInput
  rw [lexSpec input fits]
  cases h : Bowling.Grammar.spell input.data.toList with
  | none => rfl
  | some tokens =>
    simp only [Option.map_some, Option.isSome_some, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Option.getD_some, Option.bind, parseSpec]
    cases Bowling.Grammar.counts tokens <;> rfl

theorem playInputMatchesSpec : Laws.playInputMatchesSpec := by
  intro input fits
  dsimp only
  rw [playGrammar input fits]
  unfold Bowling.Grammar.Parses
  generalize h : (Bowling.Grammar.spell input.data.toList).bind Bowling.Grammar.counts = result
  cases result with
  | none => simp
  | some attempts =>
    constructor
    · simp
    · intro claimed eq
      have same : attempts = claimed := Option.some.inj eq
      subst claimed
      exact ⟨Replay attempts, rfl, fromStartMatchesRules attempts⟩

run_cmd
  for theoremName in [``goScoreBounds, ``rollAcceptedIffCompletable] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless [`propext, `Quot.sound, `Classical.choice].contains axiomName do
        throwError "Bowling proof {theoremName} depends on unapproved axiom {axiomName}"

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/bowling».Proofs
