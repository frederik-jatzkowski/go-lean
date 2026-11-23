import «compiler»

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/stack-machine-compiler».Proofs

open StackMachineCompiler.Spec

private theorem binaryEval {op : BinOp} {left right : Value}
    (hl : left.ty = op.signature.1) (hr : right.ty = op.signature.1) :
    ∃ value, op.eval left right = some value ∧ value.ty = op.signature.2 := by
  cases op <;> cases left <;> cases right <;>
    simp_all [Value.ty, BinOp.signature, BinOp.eval]

private theorem checkedEval (expr : Expr) {ty : Ty} (h : expr.check = .ok ty) :
    ∃ value, expr.eval = some value ∧ value.ty = ty := by
  induction expr generalizing ty with
  | literal v offset =>
    simp_all [Expr.check, Expr.eval]
  | binary op offset left right ihl ihr =>
    cases hr : right.check with
    | error err => simp [Expr.check, hr, Bind.bind, Except.bind] at h
    | ok rt =>
      cases hl : left.check with
      | error err => simp [Expr.check, hr, hl, Bind.bind, Except.bind] at h
      | ok lt =>
        simp [Expr.check, hr, hl, Bind.bind, Except.bind] at h
        split at h <;> simp_all [Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
        obtain ⟨l, el, tl⟩ := ihl
        obtain ⟨r, er, tr⟩ := ihr
        obtain ⟨v, ev, tv⟩ := binaryEval (op := op) (left := l) (right := r)
          (by grind) (by grind)
        exact ⟨v, by simpa [Expr.eval, el, er] using ev, by grind⟩
  | not offset e ih =>
    cases he : e.check with
    | error err => simp [Expr.check, he, Bind.bind, Except.bind] at h
    | ok et =>
      cases et <;> simp_all [Expr.check, Bind.bind, Except.bind, Pure.pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw]
      obtain ⟨v, ev, tv⟩ := ih
      subst ty
      cases v <;> simp_all [Value.ty, Expr.eval]

private theorem nextBounds {code : ByteArray} {s t : State}
    (h : StackMachineCompiler.Spec.instruction code s = .next t) (hs : s.stack.size ≤ maxInt) :
    t.pc = s.pc + 2 ∧ t.pc ≤ code.size ∧ t.stack.size ≤ maxInt := by
  unfold StackMachineCompiler.Spec.instruction at h
  dsimp only at h
  repeat' first | split at h | contradiction
  all_goals simp_all <;> subst t <;> simp_all <;> omega

private theorem boundedExecution (code : ByteArray) (s : State)
    (aligned : s.pc % 2 = 0) (bound : s.pc ≤ code.size) (hs : s.stack.size ≤ maxInt) :
    ∃ steps final status, steps + s.pc / 2 ≤ code.size / 2 + 1 ∧
      Execution code s steps final status := by
  cases h : StackMachineCompiler.Spec.instruction code s with
  | stop status => exact ⟨1, s, status, by omega, .stop h⟩
  | next t =>
    obtain ⟨eq, b, cap⟩ := nextBounds h hs
    obtain ⟨steps, final, status, count, run⟩ :=
      boundedExecution code t (by omega) b cap
    exact ⟨steps + 1, final, status, by omega, .next h run⟩
termination_by code.size - s.pc
decreasing_by omega

private def observed (r : machineResult) : UInt8 × State :=
  (r.«field:Status», ⟨r.«field:State».«field:PC».toNat, r.«field:State».«field:Stack»⟩)

private theorem stepCorrect : Requirements.stepConforms
    (fun code pc stack aligned => observed (step code ⟨pc, stack⟩ aligned)) := by
  intro code pc stack hc hs
  unfold maxInt at hc hs
  have cn : (UInt64.ofNat code.size).toNat = code.size := by
    change _ % 18446744073709551616 = _
    apply Nat.mod_eq_of_lt; omega
  have sn : (UInt64.ofNat stack.size).toNat = stack.size := by
    change _ % 18446744073709551616 = _
    apply Nat.mod_eq_of_lt; omega
  dsimp only
  unfold step StackMachineCompiler.Spec.instruction
  dsimp only
  by_cases even : pc.toNat % 2 = 0
  case neg => simp [even, observed, Requirements.Status.tag]
  by_cases outside : code.size ≤ pc.toNat
  · have endpc : code.size < pc.toNat + 2 := by omega
    simp [even, UInt64.le_iff_toNat_le, cn, outside, endpc, observed, Requirements.Status.tag]
  have le : pc ≤ UInt64.ofNat code.size := UInt64.le_iff_toNat_le.mpr (by omega)
  have rem := UInt64.toNat_sub_of_le _ _ le
  by_cases short : code.size < pc.toNat + 2
  · have lt : code.size - pc.toNat < 2 := by omega
    simp [even, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, cn, outside, rem, short, lt,
      observed, Requirements.Status.tag]
  have room : ¬code.size - pc.toNat < 2 := by omega
  have idx1 : (pc + 1).toNat = pc.toNat + 1 := by simp; omega
  have idx2 : (pc + 2).toNat = pc.toNat + 2 := by simp; omega
  have byte (i : Nat) (hi : i < code.size) : code[i]?.getD 0 = code[i]! := by
    simp [getElem?_pos, getElem!_pos, hi]
  simp only [even, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    UInt64.le_iff_toNat_le, cn, outside, decide_false, UInt64.lt_iff_toNat_lt, rem,
    UInt64.reduceToNat, room, short, ne_self_iff_false, false_or, idx1,
    byte _ (by omega : pc.toNat < code.size), byte _ (by omega : pc.toNat + 1 < code.size)]
  generalize code[pc.toNat]! = op
  by_cases bad : 7 < op
  · have large : 7 < op.toNat := bad
    have hz : op ≠ 0 := by intro h; rw [h] at large; simp at large
    have hp : op ≠ 1 := by intro h; rw [h] at large; simp at large
    have hn : op ≠ 7 := by intro h; rw [h] at large; simp at large
    have unk : binaryOp op = none := by
      unfold binaryOp
      split <;> first | rfl | (simp at large)
    simp [bad, hz, hp, hn, unk, observed, Requirements.Status.tag]
  have choices : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 := by
    simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at bad
    simp only [← UInt8.toNat_inj, UInt8.reduceToNat]
    omega
  have sub (n : UInt64) (h : n.toNat ≤ stack.size) :
      (UInt64.ofNat stack.size - n).toNat = stack.size - n.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), sn]
  rcases choices with h|h|h|h|h|h|h|h <;> subst op
  all_goals simp [observed, advance, Requirements.Status.tag, ← UInt64.toNat_inj, sn,
    maxInt, binaryOp, binaryResult, truthByte, boolByte, BinOp.rawResult, BinOp.signature,
    BinOp.eval, Value.byte]
  all_goals first
    | by_cases cap : stack.size = 9223372036854775807 <;> simp [cap, idx2] <;> done
    | by_cases few : stack.size < 2
      · simp [few]
      · have one := sub 1 (by change 1 ≤ stack.size; omega)
        have two := sub 2 (by change 2 ≤ stack.size; omega)
        simp [few, idx2, one, two, Array.back!, getElem!_pos, getElem?_pos,
          show stack.size - 1 < stack.size by omega, show stack.size - 2 < stack.size by omega]
    | by_cases empty : stack = #[]
      · simp [empty]
      · have pos : stack.size ≠ 0 := by simpa using empty
        have one := sub 1 (by change 1 ≤ stack.size; omega)
        simp [empty, idx2, one, Array.back!, getElem!_pos, getElem?_pos,
          show stack.size - 1 < stack.size by omega]

private theorem runFrom {code : ByteArray} {s final : State} {steps : Nat} {status : Status}
    (exec : Execution code s steps final status) (fuel : Nat) (idx : UInt64) (r : machineResult)
    (enough : steps ≤ fuel) (rep : (observed r).2 = s) (even : s.pc % 2 = 0)
    (hc : code.size ≤ maxInt) (hs : s.stack.size ≤ maxInt) :
    observed ((«fold».countUntil runInstruction fuel idx ⟨code,r⟩).1.«field:Result») =
      (Requirements.Status.tag status, final) := by
  induction exec generalizing fuel idx r with
  | @stop s status h =>
    cases fuel with
    | zero => omega
    | succ n =>
      rcases r with ⟨⟨pc, stack⟩, prev⟩
      subst s
      have law := stepCorrect code pc stack hc hs
      simp only [observed] at even h
      simp only [even, decide_true, h] at law
      have tag := law.1
      change (step code ⟨pc, stack⟩ true).«field:Status» = _ at tag
      have nonzero : Requirements.Status.tag status ≠ 0 := by cases status <;> decide
      simpa [«fold».countUntil, runInstruction, tag, nonzero] using Prod.ext law.1 law.2
  | @next s t n final status h _ ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rcases r with ⟨⟨pc, stack⟩, prev⟩
      subst s
      have law := stepCorrect code pc stack hc hs
      simp only [observed] at even h
      simp only [even, decide_true, h] at law
      have tag := law.1
      change (step code ⟨pc, stack⟩ true).«field:Status» = 0 at tag
      have pe := (nextBounds h hs).1
      simp only at pe
      have remaining := ih fuel (idx + 1) (step code ⟨pc, stack⟩ true) (by omega)
        law.2 (by omega) (nextBounds h hs).2.2
      simpa [«fold».countUntil, runInstruction, tag] using remaining

private theorem executionCorrect : Requirements.executionConforms (fun code => observed (runCode code)) := by
  intro code hc
  obtain ⟨steps, final, status, bound, exec⟩ := boundedExecution code ⟨0, #[]⟩ rfl (Nat.zero_le _) (Nat.zero_le _)
  have count : steps ≤ code.size / 2 + 1 := by simpa using bound
  have fuel : (UInt64.ofNat code.size + 1).toNat = code.size + 1 := by
    unfold maxInt at hc
    simp [UInt64.toNat_ofNat]; omega
  have eq := runFrom exec (code.size + 1) 0 ⟨⟨0, #[]⟩, 0⟩ (by omega) rfl rfl hc (Nat.zero_le _)
  rw [← fuel] at eq
  exact ⟨steps, final, status, count, exec, congrArg Prod.fst eq, congrArg Prod.snd eq⟩

private theorem wordsExist (source : List UInt8) (offset : Nat) :
    ∃ words, Words offset source words := by
  classical
  cases source with
  | nil => exact ⟨[], .done⟩
  | cons b tail =>
    by_cases space : whitespace b
    · obtain ⟨words, rest⟩ := wordsExist tail (offset + 1)
      exact ⟨words, .space space rest⟩
    · let keep := fun c : UInt8 => decide (¬ whitespace c)
      let bytes := b :: tail.takeWhile keep
      let rest := tail.dropWhile keep
      have partition : bytes ++ rest = b :: tail := by
        simp [bytes, rest, List.takeWhile_append_dropWhile]
      have smaller : rest.length < (b :: tail).length := by
        have := congrArg List.length partition
        simp [bytes] at this
        simp only [List.length_cons]
        omega
      obtain ⟨words, suffix⟩ := wordsExist rest (offset + bytes.length)
      refine ⟨⟨bytes, offset⟩ :: words, partition ▸ Words.word (by simp [bytes]) ?_ ?_ suffix⟩
      · intro c hc
        rcases List.mem_cons.mp hc with eq | mem
        · simpa [eq] using space
        · simpa [keep] using (List.all_eq_true.mp (List.all_takeWhile (l := tail) (p := keep)) c mem)
      · intro c hc
        have := List.head?_dropWhile_not (p := keep) (l := tail)
        change (tail.dropWhile keep).head? = some c at hc
        rw [hc] at this
        simpa [keep] using this
termination_by source.length
decreasing_by all_goals first | exact smaller | simp_wf <;> simp_all

private theorem lexOrError (words : List Word) :
    (∃ offset, FirstLexError words offset) ∨ ∃ tokens, Lexed words tokens := by
  classical
  induction words with
  | nil => exact .inr ⟨[], .done⟩
  | cons w ws ih =>
    by_cases good : ValidWord w
    · rcases ih with ⟨off, before, bad, tail, rfl, rfl, valid, invalid⟩ | ⟨ts, lex⟩
      · exact .inl ⟨_, w :: before, bad, tail, rfl, rfl, by simp_all, invalid⟩
      · obtain ⟨tok, recg⟩ := good
        exact .inr ⟨_, .token recg lex⟩
    · exact .inl ⟨_, [], w, ws, rfl, rfl, by simp, good⟩

private def readToken (located : LocatedToken) (roots : Option (List Expr)) :
    Option (List Expr) := do
  let stack ← roots
  let (token, offset) := located
  match token, stack with
  | .literal value, rest => some (.literal value offset :: rest)
  | .not, e :: rest => some (.not offset e :: rest)
  | .binary op, l :: r :: rest => some (.binary op offset l r :: rest)
  | _, _ => none

private theorem readExpr (e : Expr) (rest : List Expr) :
    e.tokens.foldr readToken (some rest) = some (e :: rest) := by
  induction e generalizing rest with
  | literal => rfl
  | not off e ih => simp [Expr.tokens, ih, readToken]
  | binary op off l r il ir => simp [Expr.tokens, List.foldr_append, il, ir, readToken]

private theorem readTokensSound (ts : List LocatedToken) (roots : List Expr)
    (h : ts.foldr readToken (some []) = some roots) :
    roots.flatMap Expr.tokens = ts := by
  induction ts generalizing roots with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases ht : ts.foldr readToken (some []) with
    | none => simp [ht, readToken] at h
    | some stack =>
      have tailTokens := ih stack ht
      obtain ⟨token, off⟩ := t
      cases token <;> cases stack <;> simp [ht, readToken] at h
      all_goals first
        | subst roots; simp_all [Expr.tokens]
        | split at h <;> simp_all <;> subst roots <;> simp_all [Expr.tokens, List.append_assoc]

private theorem parseTokensIff (ts : List LocatedToken) (e : Expr) :
    ts.foldr readToken (some []) = some [e] ↔ e.tokens = ts := by
  constructor
  · intro h
    simpa using readTokensSound ts [e] h
  · rintro rfl
    exact readExpr e []

private theorem outcomeExists (src : List UInt8) : ∃ outcome, SourceOutcome src outcome := by
  classical
  obtain ⟨words, splitWords⟩ := wordsExist src 0
  rcases lexOrError words with ⟨off, err⟩ | ⟨ts, lex⟩
  · exact ⟨_, .lexical splitWords err⟩
  · by_cases parsed : ∃ expr : Expr, ts.foldr readToken (some []) = some [expr]
    · obtain ⟨expr, parsed⟩ := parsed
      obtain rfl := (parseTokensIff ts expr).mp parsed
      cases h : expr.check with
      | error offset => exact ⟨_, .typeMismatch splitWords lex h⟩
      | ok ty =>
        by_cases fits : 2 * expr.tokens.length + 2 ≤ maxInt
        · exact ⟨_, .success splitWords lex h fits⟩
        · exact ⟨_, .codeTooLarge splitWords lex h (by omega)⟩
    · exact ⟨_, .syntax splitWords lex (fun ⟨e, he⟩ => parsed ⟨e, (parseTokensIff ts e).mpr he⟩)⟩

private def tokenClass : Token → classification
  | .literal (.number n) => ⟨1, n⟩
  | .literal (.boolean b) => ⟨2, boolByte b⟩
  | .binary .add => ⟨3, 0⟩
  | .binary .sub => ⟨4, 0⟩
  | .binary .eq => ⟨5, 0⟩
  | .binary .lt => ⟨6, 0⟩
  | .binary .and => ⟨7, 0⟩
  | .not => ⟨8, 0⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem classifyRecognized (word : ByteArray) (tok : Token)
    (h : Recognizes word.data.toList tok) : classify word = tokenClass tok := by
  have bytes {s : String} (eq : word.data.toList = ascii s) : word = s.toUTF8 := by
    cases word
    congr
    exact Array.toList_inj.mp eq
  cases tok with
  | not => rw [bytes h]; rfl
  | binary op => cases op <;> rw [bytes h] <;> rfl
  | literal v =>
    cases v with
    | boolean b => cases b <;> rw [bytes h] <;> rfl
    | number n =>
      rw [bytes h]
      have decimalTable : ∀ i : Fin 256,
          let result := classify (toString i.val).toUTF8
          result.«field:Kind» = 1 ∧ result.«field:Value» = UInt8.ofNat i.val := by decide
      obtain ⟨kind, value⟩ := decimalTable n.toBitVec.toFin
      change (classify (toString n.toNat).toUTF8).«field:Kind» = 1 at kind
      change (classify (toString n.toNat).toUTF8).«field:Value» = UInt8.ofNat n.toNat at value
      simp only [UInt8.ofNat_toNat] at value
      generalize classify (toString n.toNat).toUTF8 = result at *
      cases result
      congr <;> assumption

private def compileResult (source : ByteArray) : Requirements.Compilation :=
  let r := compile source
  ⟨r.«field:Code», r.«field:Type», r.«field:Error».«field:Kind», r.«field:Error».«field:Offset».toNat⟩

private inductive Steps (code : ByteArray) : State → State → Prop where
  | refl : Steps code s s
  | cons : StackMachineCompiler.Spec.instruction code s = .next t → Steps code t u → Steps code s u

private theorem Steps.trans {code : ByteArray} {s t u : State}
    (a : Steps code s t) (b : Steps code t u) : Steps code s u := by
  induction a with
  | refl => exact b
  | cons h _ ih => exact .cons h (ih b)

private theorem Steps.finish {code : ByteArray} {s t : State} (a : Steps code s t)
    {status : Status} (h : StackMachineCompiler.Spec.instruction code t = .stop status) :
    ∃ n, Execution code s n t status := by
  induction a with
  | refl => exact ⟨_, .stop h⟩
  | cons step _ ih => obtain ⟨n, e⟩ := ih h; exact ⟨_, .next step e⟩

private theorem executionUnique {code : ByteArray} {s t u : State} {m n : Nat} {a b : Status}
    (first : Execution code s m t a) (second : Execution code s n u b) : t = u ∧ a = b := by
  induction first generalizing n u b with
  | stop h => cases second <;> grind
  | next h _ ih => cases second <;> grind

private theorem instLength (e : Expr) : e.instructions.length = 2 * e.tokens.length := by
  induction e <;> simp_all [Expr.instructions, Expr.tokens] <;> omega

private theorem pairAt (code : ByteArray) (pre post : List UInt8) (op arg : UInt8)
    (layout : code.data.toList = pre ++ op :: arg :: post) :
    pre.length + 2 ≤ code.size ∧ code[pre.length]! = op ∧ code[pre.length + 1]! = arg := by
  have len := congrArg List.length layout
  simp only [Array.length_toList, List.length_append, List.length_cons] at len
  have room : pre.length + 2 ≤ code.size := by change _ ≤ code.data.size; omega
  refine ⟨room, ?_, ?_⟩
  all_goals rw [getElem!_pos _ _ (by omega), ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
  all_goals simp [layout, List.getElem_append_right]

private theorem replaceTop (s : Array UInt8) (a b : UInt8) :
    (s.push a).setIfInBounds s.size b = s.push b := by
  simp [Array.setIfInBounds, Array.set_push]

private theorem secondTop (s : Array UInt8) (a b : UInt8) :
    ((s.push a).push b)[s.size]! = a := by
  simp [getElem!_pos, Array.getElem_push, show s.size < s.size + 1 + 1 by omega]

private theorem runBinary (op : BinOp) (left right value : Value)
    (ev : op.eval left right = some value) (code : ByteArray) (pc : Nat) (stack : Array UInt8)
    (even : pc % 2 = 0) (room : pc + 2 ≤ code.size) (byte : code[pc]! = op.opcode) :
    StackMachineCompiler.Spec.instruction code ⟨pc, (stack.push right.byte).push left.byte⟩ =
      .next ⟨pc + 2, stack.push value.byte⟩ := by
  have pair : ¬code.size < pc + 2 := by omega
  cases op <;> cases left <;> cases right <;> simp [BinOp.eval] at ev <;> subst value
  all_goals simp [StackMachineCompiler.Spec.instruction, even, pair, byte, BinOp.opcode, binaryOp,
    BinOp.rawResult, BinOp.signature, BinOp.eval, Value.byte, boolByte]
  all_goals split <;> simp_all [secondTop, replaceTop] <;> first | omega | (rename_i a b; cases a <;> cases b <;> decide)

private theorem evalSteps (e : Expr) (v : Value) (ev : e.eval = some v)
    (code : ByteArray) (pre post : List UInt8) (stack : Array UInt8)
    (layout : code.data.toList = pre ++ e.instructions ++ post)
    (even : pre.length % 2 = 0) (cap : stack.size + e.tokens.length ≤ maxInt) :
    Steps code ⟨pre.length, stack⟩ ⟨pre.length + e.instructions.length, stack.push v.byte⟩ := by
  induction e generalizing pre post stack v with
  | literal value off =>
    cases ev
    have ⟨room, op, arg⟩ := pairAt code pre post 1 value.byte (by simpa [Expr.instructions, List.append_assoc] using layout)
    apply Steps.cons (t := ⟨pre.length + 2, stack.push value.byte⟩) _ .refl
    simp [StackMachineCompiler.Spec.instruction, even, show ¬code.size < pre.length + 2 by omega,
      op, arg, show stack.size ≠ maxInt by simp [Expr.tokens] at cap; omega]
  | not off e ih =>
    cases he : e.eval with
    | none => simp [Expr.eval, he] at ev
    | some arg =>
      cases arg with
      | number n => simp [Expr.eval, he] at ev
      | boolean b =>
        simp [Expr.eval, he] at ev
        subst v
        have sub := ih (.boolean b) he pre ([7, 0] ++ post) stack
          (by simpa [Expr.instructions, List.append_assoc] using layout) even (by simp [Expr.tokens] at cap; omega)
        let before := pre ++ e.instructions
        have ⟨room, op, _⟩ := pairAt code before post 7 0 (by simpa [before, Expr.instructions, List.append_assoc] using layout)
        have aligned : before.length % 2 = 0 := by simp [before, instLength]; omega
        have step : StackMachineCompiler.Spec.instruction code ⟨before.length, stack.push (Value.boolean b).byte⟩ =
            .next ⟨before.length + 2, stack.push (Value.boolean (!b)).byte⟩ := by
          cases b <;> simp [StackMachineCompiler.Spec.instruction, aligned, show ¬code.size < before.length + 2 by omega,
            op, Value.byte, boolByte, replaceTop]
        apply sub.trans
        simpa [before, Expr.instructions, Nat.add_assoc] using Steps.cons step Steps.refl
  | binary op off l r il ir =>
    cases hl : l.eval with
    | none => simp [Expr.eval, hl] at ev
    | some lv =>
      cases hr : r.eval with
      | none => simp [Expr.eval, hl, hr] at ev
      | some rv =>
        simp [Expr.eval, hl, hr] at ev
        let middle := pre ++ r.instructions
        let before := middle ++ l.instructions
        have right := ir rv hr pre (l.instructions ++ [op.opcode, 0] ++ post) stack
          (by simpa [Expr.instructions, List.append_assoc] using layout) even (by simp [Expr.tokens] at cap; omega)
        have left := il lv hl middle ([op.opcode, 0] ++ post) (stack.push rv.byte)
          (by simpa [middle, Expr.instructions, List.append_assoc] using layout)
          (by simp [middle, instLength]; omega) (by simp [Expr.tokens] at cap; simp; omega)
        have ⟨room, opcode, _⟩ := pairAt code before post op.opcode 0
          (by simpa [before, middle, Expr.instructions, List.append_assoc] using layout)
        have finish := runBinary op lv rv v ev code before.length stack
          (by simp [before, middle, instLength]; omega) room opcode
        apply right.trans
        apply Steps.trans (by simpa [middle] using left)
        simpa [before, middle, Expr.instructions, Nat.add_assoc] using Steps.cons finish Steps.refl

private theorem preservesMeaning (cc : Requirements.compilationConforms compileResult) :
    Requirements.preservesSourceMeaning compileResult (fun code => observed (runCode code)) := by
  intro src e ty fits success
  have exactCode := ((cc src fits).2 _ success).2.2.2
  cases success with
  | success words lex check cap =>
    obtain ⟨v, ev, vt⟩ := checkedEval e check
    let code := (compileResult src).code
    have layout : code.data.toList = e.instructions ++ [0, 0] := exactCode
    have bytes := congrArg List.length layout
    simp [instLength] at bytes
    have repr : code.size ≤ maxInt := by omega
    have path := evalSteps e v ev code [] [0, 0] #[] (by simpa using layout) rfl (by simp; omega)
    have ⟨room, halt, _⟩ := pairAt code e.instructions [] 0 0 layout
    have stopped : StackMachineCompiler.Spec.instruction code ⟨e.instructions.length, #[v.byte]⟩ =
        .stop .halt := by
      simp [StackMachineCompiler.Spec.instruction, halt, show ¬code.size < e.instructions.length + 2 by omega,
        show e.instructions.length % 2 = 0 by rw [instLength]; omega]
    obtain ⟨_, expected⟩ := path.finish (by simpa using stopped)
    obtain ⟨_, final, status, _, actual, tag, state⟩ := executionCorrect code repr
    obtain ⟨rfl, rfl⟩ := executionUnique actual expected
    exact ⟨v, ev, vt, tag, by simpa [instLength] using congrArg State.pc state, congrArg State.stack state⟩

private theorem sizeNat {n : Nat} (fits : n ≤ maxInt) : (UInt64.ofNat n).toNat = n := by
  change n % 18446744073709551616 = n
  apply Nat.mod_eq_of_lt
  unfold maxInt at fits; omega

private def locatedLexeme (t : LocatedToken) : lexeme :=
  let c := tokenClass t.1
  ⟨c.«field:Kind», c.«field:Value», UInt64.ofNat t.2⟩

private theorem tokenKindNonzero (t : Token) : (tokenClass t).«field:Kind» ≠ 0 := by
  cases t with
  | literal v => cases v <;> simp [tokenClass]
  | binary op => cases op <;> decide
  | not => decide

private theorem scannerSpace (b : UInt8) : isSpace b = true ↔ whitespace b := by
  simp [isSpace, whitespace, or_assoc]

private theorem byteAtList (data : ByteArray) (i : Nat) : data[i]? = data.data.toList[i]? := by
  by_cases h : i < data.size
  · simp [getElem?_pos, h, ByteArray.getElem_eq_getElem_data, ByteArray.size_data]
  · simp [getElem?_neg, h, ByteArray.size_data]

private def digitByte (i : Fin 10) : UInt8 := UInt8.ofNat (48 + i.val)

private theorem digitByteExists (b : UInt8) (digit : isDigit b = true) :
    ∃ i, digitByte i = b := by
  have bounds : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
    simpa [isDigit, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] using digit
  refine ⟨⟨b.toNat - 48, by omega⟩, ?_⟩
  have eq : 48 + (b.toNat - 48) = b.toNat := by omega
  simp [digitByte, eq]

private theorem decimalOne (a : UInt8) (accepted : (decimal a 0 0 1).«field:Kind» ≠ 0) :
    Recognizes [a] (.literal (.number (decimal a 0 0 1).«field:Value»)) := by
  have digit : isDigit a = true := by
    cases h : isDigit a <;> simp_all [decimal]
  obtain ⟨i, rfl⟩ := digitByteExists a digit
  exact (show ∀ i : Fin 10, Recognizes [digitByte i]
    (.literal (.number (decimal (digitByte i) 0 0 1).«field:Value»)) by
    simp only [Recognizes]
    decide) i

private theorem decimalTwo (a b : UInt8) (accepted : (decimal a b 0 2).«field:Kind» ≠ 0) :
    Recognizes [a, b] (.literal (.number (decimal a b 0 2).«field:Value»)) := by
  have digits : isDigit a = true ∧ isDigit b = true := by
    cases ha : isDigit a <;> cases hb : isDigit b <;> simp_all [decimal]
  obtain ⟨i, rfl⟩ := digitByteExists a digits.1
  obtain ⟨j, rfl⟩ := digitByteExists b digits.2
  exact (show ∀ i j : Fin 10, (decimal (digitByte i) (digitByte j) 0 2).«field:Kind» ≠ 0 →
    Recognizes [digitByte i, digitByte j]
      (.literal (.number (decimal (digitByte i) (digitByte j) 0 2).«field:Value»)) by
    simp only [Recognizes]
    decide) i j accepted

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem decimalThree (a b c : UInt8) (accepted : (decimal a b c 3).«field:Kind» ≠ 0) :
    Recognizes [a, b, c] (.literal (.number (decimal a b c 3).«field:Value»)) := by
  have digits : isDigit a = true ∧ isDigit b = true ∧ isDigit c = true := by
    cases ha : isDigit a <;> cases hb : isDigit b <;> cases hc : isDigit c <;>
      simp_all [decimal] <;> split at accepted <;> simp_all
  obtain ⟨i, rfl⟩ := digitByteExists a digits.1
  obtain ⟨j, rfl⟩ := digitByteExists b digits.2.1
  obtain ⟨k, rfl⟩ := digitByteExists c digits.2.2
  exact (show ∀ i j k : Fin 10, (decimal (digitByte i) (digitByte j) (digitByte k) 3).«field:Kind» ≠ 0 →
    Recognizes [digitByte i, digitByte j, digitByte k]
      (.literal (.number (decimal (digitByte i) (digitByte j) (digitByte k) 3).«field:Value»)) by
    simp only [Recognizes]
    decide) i j k accepted

set_option linter.unusedSimpArgs false in
private theorem classifyValid (data : ByteArray) (fits : data.size ≤ maxInt)
    (accepted : (classify data).«field:Kind» ≠ 0) :
    ∃ tok, Recognizes data.data.toList tok := by
  have width : (UInt64.ofNat data.size).toNat = data.size := sizeNat fits
  simp only [classify, byteAtList] at accepted
  have wide (h : 5 < data.size) : False := by
    have ne (n : UInt64) (small : n.toNat ≤ 5) : UInt64.ofNat data.size ≠ n := by
      intro eq
      have := congrArg UInt64.toNat eq
      omega
    simp [ne 2 (by decide), ne 3 (by decide), ne 4 (by decide), ne 5 (by decide)] at accepted
    unfold decimal at accepted
    split at accepted
    · simp [← ByteArray.size_data, Array.size_eq_length_toList] at accepted
    · simp [ne 1 (by decide), ne 2 (by decide), ne 3 (by decide)] at accepted
  cases data with
  | mk arr =>
    cases arr with
    | mk bytes =>
      change ∃ tok, Recognizes bytes tok
      cases bytes with
      | nil => simp [← ByteArray.size_data, Array.size_eq_length_toList, decimal, isDigit] at accepted
      | cons a tail =>
        cases tail with
        | nil =>
          simp [← ByteArray.size_data, Array.size_eq_length_toList] at accepted
          exact ⟨_, decimalOne a accepted⟩
        | cons b tail =>
          cases tail with
          | nil =>
            simp [← ByteArray.size_data, Array.size_eq_length_toList] at accepted
            split at accepted
            · rename_i eq
              rcases eq with ⟨rfl, rfl⟩
              exact ⟨.binary .eq, rfl⟩
            · split at accepted
              · rename_i eq
                rcases eq with ⟨rfl, rfl⟩
                exact ⟨.binary .lt, rfl⟩
              · exact ⟨_, decimalTwo a b accepted⟩
          | cons c tail =>
            cases tail with
            | nil =>
              simp [← ByteArray.size_data, Array.size_eq_length_toList] at accepted
              split at accepted
              · rename_i eq
                rcases eq with ⟨⟨rfl, rfl⟩, rfl⟩
                exact ⟨.binary .add, rfl⟩
              · split at accepted
                · rename_i eq
                  rcases eq with ⟨⟨rfl, rfl⟩, rfl⟩
                  exact ⟨.binary .sub, rfl⟩
                · split at accepted
                  · rename_i eq
                    rcases eq with ⟨⟨rfl, rfl⟩, rfl⟩
                    exact ⟨.binary .and, rfl⟩
                  · split at accepted
                    · rename_i eq
                      rcases eq with ⟨⟨rfl, rfl⟩, rfl⟩
                      exact ⟨.not, rfl⟩
                    · exact ⟨_, decimalThree a b c accepted⟩
            | cons d tail =>
              cases tail with
              | nil =>
                simp [← ByteArray.size_data, Array.size_eq_length_toList] at accepted
                split at accepted
                · rename_i eq
                  rcases eq with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
                  exact ⟨.literal (.boolean true), rfl⟩
                · simp [decimal] at accepted
              | cons e tail =>
                cases tail with
                | nil =>
                  simp [← ByteArray.size_data, Array.size_eq_length_toList] at accepted
                  split at accepted
                  · rename_i eq
                    rcases eq with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
                    exact ⟨.literal (.boolean false), rfl⟩
                  · simp [decimal] at accepted
                | cons f tail => exact False.elim (wide (by simp [← ByteArray.size_data, Array.size_eq_length_toList] <;> omega))

private theorem closeRecognizedWord (source : ByteArray) (start stop : UInt64)
    (words : Array lexeme) (error : diagnostic) (oldScan : scanState)
    (token : Token) (recognized : Recognizes (source.extract start.toNat stop.toNat).data.toList token) :
    closeWord stop ⟨source, words, oldScan, error⟩ ⟨start, false⟩ =
      (⟨source, words.push ⟨(tokenClass token).«field:Kind», (tokenClass token).«field:Value», start⟩,
        ⟨start, false⟩, error⟩, false) := by
  simp [closeWord, classifyRecognized _ token recognized, tokenKindNonzero token]

private theorem scanNonspace (source : ByteArray) (i : UInt64) (words : Array lexeme)
    (start : UInt64) (inside : Bool) (error : diagnostic) (byte : UInt8)
    (atByte : source[i.toNat]? = some byte) (nonspace : ¬ whitespace byte) :
    scanSourceByte i ⟨source, words, ⟨start, inside⟩, error⟩ =
      (⟨source, words, ⟨if inside then start else i, true⟩, error⟩, false) := by
  have h : isSpace byte = false := by
    cases space : isSpace byte
    · rfl
    · exact False.elim (nonspace ((scannerSpace byte).mp space))
  cases inside <;> simp [scanSourceByte, scanByte, atByte, h]

private theorem scanWordBytes (source : ByteArray) (i start : UInt64)
    (words : Array lexeme) (error : diagnostic) (bytes tail : List UInt8)
    (suffix : source.data.toList.drop i.toNat = bytes ++ tail)
    (fits : source.size ≤ maxInt) (nonspace : ∀ b ∈ bytes, ¬ whitespace b) :
    («fold».countUntil scanSourceByte bytes.length i
        ⟨source, words, ⟨start, true⟩, error⟩) =
      (⟨source, words, ⟨start, true⟩, error⟩, false) := by
  induction bytes generalizing i with
  | nil => rfl
  | cons b bs ih =>
    have atByte : source[i.toNat]? = some b := by
      rw [byteAtList, ← List.head?_drop, suffix]
      rfl
    have lt : i.toNat < source.size := by
      have := getElem?_eq_some_iff.mp atByte
      exact this.choose
    have inc : (i + 1).toNat = i.toNat + 1 := by
      unfold maxInt at fits
      simp
      omega
    have rest : source.data.toList.drop (i + 1).toNat = bs ++ tail := by
      rw [inc, List.drop_add_one_eq_tail_drop, suffix]
      rfl
    rw [List.length_cons, «fold».countUntil, scanNonspace source i words start true error b atByte
      (nonspace b (by simp))]
    exact ih (i + 1) rest (fun c mem => nonspace c (by simp [mem]))
private theorem scanDelimiter (source : ByteArray) (i start : UInt64) (words : Array lexeme)
    (inside : Bool) (error : diagnostic) (byte : UInt8)
    (atByte : source[i.toNat]? = some byte) (space : whitespace byte) :
    scanSourceByte i ⟨source, words, ⟨start, inside⟩, error⟩ =
      if inside then closeWord i ⟨source, words, ⟨start, true⟩, error⟩ ⟨start, false⟩
      else (⟨source, words, ⟨start, false⟩, error⟩, false) := by
  cases inside <;> simp [scanSourceByte, scanByte, atByte, (scannerSpace byte).mpr space]

private theorem scanFoldAppend {S : Type} (step : UInt64 → S → S × Bool)
    (n m : Nat) (i : UInt64) (state : S) :
    «fold».countUntil step (n + m) i state =
      let first := «fold».countUntil step n i state
      if first.2 then first else «fold».countUntil step m (i + UInt64.ofNat n) first.1 := by
  induction n generalizing i state with
  | zero => simp [«fold».countUntil]
  | succ n ih =>
    rw [Nat.succ_add, «fold».countUntil, «fold».countUntil]
    cases step i state with
    | mk s stop =>
      cases stop with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [ih, UInt64.ofNat_add]
        have advance : i + 1 + UInt64.ofNat n = i + (UInt64.ofNat n + 1) := by rw [UInt64.add_assoc, UInt64.add_comm (1 : UInt64)]
        rw [advance]; rfl
      | true => rfl

private theorem scanWordStart (source : ByteArray) (i start : UInt64)
    (words : Array lexeme) (error : diagnostic) (b : UInt8) (bytes tail : List UInt8)
    (suffix : source.data.toList.drop i.toNat = (b :: bytes) ++ tail)
    (fits : source.size ≤ maxInt) (nonspace : ∀ c ∈ b :: bytes, ¬ whitespace c) :
    («fold».countUntil scanSourceByte (b :: bytes).length i
        ⟨source, words, ⟨start, false⟩, error⟩) =
      (⟨source, words, ⟨i, true⟩, error⟩, false) := by
  have atByte : source[i.toNat]? = some b := by
    rw [byteAtList, ← List.head?_drop, suffix]
    rfl
  have lt := (getElem?_eq_some_iff.mp atByte).choose
  have inc : (i + 1).toNat = i.toNat + 1 := by
    unfold maxInt at fits
    simp
    omega
  have rest : source.data.toList.drop (i + 1).toNat = bytes ++ tail := by
    rw [inc, List.drop_add_one_eq_tail_drop, suffix]
    rfl
  rw [List.length_cons, «fold».countUntil, scanNonspace source i words start false error b atByte
    (nonspace b (by simp))]
  exact scanWordBytes source (i + 1) i words error bytes tail rest fits (fun c mem => nonspace c (by simp [mem]))
private def finishScan (sourceSize : UInt64) (scanned : lexer × Bool) : lexer :=
  if scanned.2 || !scanned.1.«field:Scan».«field:InWord» then scanned.1
  else (closeWord sourceSize scanned.1 ⟨scanned.1.«field:Scan».«field:Start», false⟩).1

private theorem scanRecognized (source : ByteArray) (fits : source.size ≤ maxInt)
    {offset : Nat} {bytes : List UInt8} {words : List Word} (splitWords : Words offset bytes words)
    (suffix : source.data.toList.drop offset = bytes) (length : offset + bytes.length = source.size)
    (tokens : List LocatedToken) (lexed : Lexed words tokens)
    (prior : Array lexeme) (start : UInt64) (err : diagnostic) :
    let result := finishScan (UInt64.ofNat source.size)
      («fold».countUntil scanSourceByte bytes.length (UInt64.ofNat offset)
        ⟨source, prior, ⟨start, false⟩, err⟩)
    result.«field:Words».toList = prior.toList ++ tokens.map locatedLexeme ∧
      result.«field:Error» = err := by
  induction splitWords generalizing tokens prior start with
  | done =>
    cases lexed
    simp [finishScan, «fold».countUntil]
  | @space b off tail ws space _ ih =>
    have offFit : off ≤ maxInt := by simp at length; omega
    have atByte : source[(UInt64.ofNat off).toNat]? = some b := by
      rw [sizeNat offFit, byteAtList, ← List.head?_drop, suffix]
      rfl
    have rest : source.data.toList.drop (off + 1) = tail := by
      rw [List.drop_add_one_eq_tail_drop, suffix]
      rfl
    rw [List.length_cons, «fold».countUntil,
      scanDelimiter source (UInt64.ofNat off) start prior false err b atByte space]
    simpa using ih rest (by simp at length; omega) tokens lexed prior start
  | @word w off tail ws nonempty nonspace boundary _ ih =>
    cases lexed with
    | @token tok _ ts _ recognized rest =>
      cases w with
      | nil => contradiction
      | cons b bs =>
        let w := b :: bs
        let next := off + w.length
        let j := UInt64.ofNat next
        let i := UInt64.ofNat off
        have iFit : off ≤ maxInt := by simp at length; omega
        have jFit : next ≤ maxInt := by simp [next, w] at length ⊢; omega
        have il : i.toNat = off := sizeNat iFit
        have jl : j.toNat = next := sizeNat jFit
        have restBytes : source.data.toList.drop next = tail := by
          dsimp only [next]
          rw [← List.drop_drop, suffix, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
        have recognizedSlice : Recognizes (source.extract i.toNat j.toNat).data.toList tok := by
          rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop, il, jl, suffix]
          have width : next - off = w.length := by simp [next]
          rw [width, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
          exact recognized
        let word := locatedLexeme (tok, off)
        let closed : lexer := ⟨source, prior.push word, ⟨i, false⟩, err⟩
        have closing : closeWord j ⟨source, prior, ⟨i, true⟩, err⟩ ⟨i, false⟩ =
            (closed, false) :=
          closeRecognizedWord source i j prior err ⟨i, true⟩ tok recognizedSlice
        have scan := scanWordStart source i start prior err b bs tail (by simpa only [il] using suffix) fits nonspace
        rw [List.length_append, scanFoldAppend, scan]
        simp only [Bool.false_eq_true, ite_false]
        rw [← UInt64.ofNat_add]
        have advance :
            finishScan (UInt64.ofNat source.size)
              («fold».countUntil scanSourceByte tail.length j ⟨source, prior, ⟨i, true⟩, err⟩) =
            finishScan (UInt64.ofNat source.size)
              («fold».countUntil scanSourceByte tail.length j closed) := by
          cases tail with
          | nil =>
            have endAt : UInt64.ofNat source.size = j := by
              congr 1
              simp [next, w] at length ⊢
              omega
            simp [«fold».countUntil, endAt, finishScan, closing, closed]
          | cons d ds =>
            have atByte : source[j.toNat]? = some d := by
              rw [jl, byteAtList, ← List.head?_drop, restBytes]
              rfl
            have space := boundary d rfl
            rw [List.length_cons, «fold».countUntil, «fold».countUntil,
              scanDelimiter source j i prior true err d atByte space,
              show scanSourceByte j closed = (closed, false) from
                scanDelimiter source j i (prior.push word) false err d atByte space]
            simp [closing]
        rw [advance]
        have eq := ih restBytes (by simp at length ⊢; omega) ts rest (prior.push word) i
        simpa only [closed, word, Array.toList_push, List.append_assoc, List.singleton_append, List.map_cons] using eq

private theorem tokenizeRecognized (source : ByteArray) (fits : source.size ≤ maxInt)
    (words : List Word) (tokens : List LocatedToken)
    (splitWords : Words 0 source.data.toList words) (lexed : Lexed words tokens) :
    (tokenize source).«field:Words».toList = tokens.map locatedLexeme ∧
      (tokenize source).«field:Error» = noDiagnostic := by
  have eq := scanRecognized source fits splitWords (by simp) (by simp [ByteArray.size_data]) tokens lexed
    #[] 0 noDiagnostic
  unfold tokenize
  rw [sizeNat fits]
  simpa [finishScan, Bool.or_eq_true] using eq
private def modelExpr : Expr → expression
  | .literal v offset => leaf (locatedLexeme (.literal v, offset))
  | .not offset operand => .mk (locatedLexeme (.not, offset)) (some (modelExpr operand)) none
  | .binary op offset left right =>
      .mk (locatedLexeme (.binary op, offset)) (some (modelExpr left)) (some (modelExpr right))

private def modelRoots : List Expr → Array expression
  | [] => #[]
  | e :: rest => (modelRoots rest).push (modelExpr e)

@[simp] private theorem modelRootsSize (roots : List Expr) : (modelRoots roots).size = roots.length := by
  induction roots <;> simp_all [modelRoots]

private def viewParse (result : parser × Bool) : Option (Array expression) :=
  if result.2 then none else some result.1.«field:Roots»

set_option linter.unusedSimpArgs false in
private theorem parseStep (words : Array lexeme) (index : UInt64) (t : LocatedToken)
    (atWord : words[(UInt64.ofNat words.size - 1 - index).toNat]? = some (locatedLexeme t))
    (roots : List Expr) (fits : roots.length ≤ maxInt) :
    viewParse (parseWord index ⟨words, modelRoots roots⟩) =
      (readToken t (some roots)).map modelRoots := by
  obtain ⟨tok, offset⟩ := t
  have last (e : Expr) (rest : List Expr) (bound : rest.length + 1 ≤ maxInt) :
      ((modelRoots rest).push (modelExpr e))[(UInt64.ofNat (rest.length + 1) - 1).toNat]? =
        some (modelExpr e) := by
    have eq : UInt64.ofNat (rest.length + 1) - 1 = UInt64.ofNat rest.length := by
      rw [UInt64.ofNat_add]; simp
    rw [eq, sizeNat (show rest.length ≤ maxInt by omega)]
    rw [← modelRootsSize rest]
    exact Array.getElem?_push_size
  have previous (l r : Expr) (rest : List Expr) (bound : rest.length + 1 + 1 ≤ maxInt) :
      (((modelRoots rest).push (modelExpr r)).push (modelExpr l))[(UInt64.ofNat (rest.length + 1 + 1) - 2).toNat]? = some (modelExpr r) := by
    have eq : UInt64.ofNat (rest.length + 1 + 1) - 2 = UInt64.ofNat rest.length := by
      rw [show rest.length + 1 + 1 = rest.length + 2 by omega, UInt64.ofNat_add]; simp
    rw [eq, sizeNat (show rest.length ≤ maxInt by omega)]
    rw [← modelRootsSize rest]
    rw [Array.getElem?_push, ite_eq_right (by simp)]
    exact Array.getElem?_push_size
  cases tok with
  | literal v =>
    cases v <;> simp [parseWord, atWord, locatedLexeme, tokenClass, arity, viewParse, readToken, modelRoots, modelExpr]
  | not =>
    cases roots with
    | nil => simp [parseWord, atWord, locatedLexeme, tokenClass, arity, viewParse, readToken, modelRoots]
    | cons e rest =>
      simp only [List.length_cons] at fits
      simp only [parseWord, atWord, Option.getD_some, locatedLexeme, tokenClass,
        arity, lexeme.«field:Kind», modelRoots, Array.size_push, modelRootsSize]
      simp only [last e rest fits, UInt64.lt_iff_toNat_lt, sizeNat fits]
      simp [viewParse, readToken, modelRoots, modelExpr, tokenClass, locatedLexeme]
  | binary op =>
    cases roots with
    | nil =>
      cases op <;> simp [parseWord, atWord, locatedLexeme, tokenClass, arity, viewParse, readToken, modelRoots]
    | cons l tail =>
      cases tail with
      | nil =>
        cases op <;> simp [parseWord, atWord, locatedLexeme, tokenClass, arity, viewParse, readToken, modelRoots]
      | cons r rest =>
        simp only [List.length_cons] at fits
        have top := last l (r :: rest) fits
        simp only [List.length_cons, modelRoots] at top
        cases op <;>
          simp only [parseWord, atWord, Option.getD_some, locatedLexeme, tokenClass,
            arity, lexeme.«field:Kind», modelRoots, Array.size_push, modelRootsSize]
        all_goals simp only [top, previous l r rest fits, UInt64.lt_iff_toNat_lt, sizeNat fits]
        all_goals simp [viewParse, readToken, modelRoots, modelExpr, locatedLexeme, tokenClass, show ¬ rest.length + 1 + 1 < 2 by omega]

private theorem parseCorresponds (words : Array lexeme) (tokens : List LocatedToken)
    (layout : words.toList = tokens.map locatedLexeme) (fits : words.size ≤ maxInt)
    (remaining : Nat) (index : UInt64) (roots : List Expr)
    (rootsBound : roots.length ≤ index.toNat) (count : index.toNat + remaining = words.size) :
    viewParse («fold».countUntil parseWord remaining index ⟨words, modelRoots roots⟩) =
      ((tokens.take remaining).foldr readToken (some roots)).map modelRoots := by
  have lengths : words.size = tokens.length := by simpa using congrArg List.length layout
  induction remaining generalizing index roots with
  | zero => simp [«fold».countUntil, viewParse]
  | succ n ih =>
    have wn := sizeNat fits
    have first : (1 : UInt64) ≤ UInt64.ofNat words.size :=
      UInt64.le_iff_toNat_le.mpr (by change 1 ≤ _; omega)
    have dif := UInt64.toNat_sub_of_le _ _ first
    have second : index ≤ UInt64.ofNat words.size - 1 :=
      UInt64.le_iff_toNat_le.mpr (by rw [dif, wn]; change _ ≤ words.size - 1; omega)
    have pos : (UInt64.ofNat words.size - 1 - index).toNat = n := by
      rw [UInt64.toNat_sub_of_le _ _ second, dif, wn]
      change words.size - 1 - _ = n
      omega
    have hn : n < tokens.length := by omega
    let t := tokens[n]
    have atWord : words[n]? = some (locatedLexeme t) := by
      have atIndex := congrArg (fun xs : List lexeme => xs[n]?) layout
      simpa [List.getElem?_map, getElem?_pos tokens n hn, t] using atIndex
    have step := parseStep words index t (by rw [pos]; exact atWord) roots (by omega)
    have take : tokens.take (n + 1) = tokens.take n ++ [t] := by
      rw [List.take_add_one, getElem?_pos tokens n hn]; rfl
    rw [take, List.foldr_append]
    change _ = ((tokens.take n).foldr readToken (readToken t (some roots))).map modelRoots
    let result := parseWord index ⟨words, modelRoots roots⟩
    have sameWords : result.1.«field:Words» = words := by
      simp only [result, parseWord]
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
    have inc : (index + 1).toNat = index.toNat + 1 := by
      unfold maxInt at fits
      simp
      omega
    change viewParse result = _ at step
    rw [«fold».countUntil]
    change viewParse (if result.2 then result else «fold».countUntil parseWord n (index + 1) result.1) = _
    cases h : readToken t (some roots) with
    | none =>
      have stopped : result.2 = true := by
        cases r : result.2 <;> simp [viewParse, r, h] at step ⊢
      have propagate (xs : List LocatedToken) : xs.foldr readToken none = none := by
        induction xs <;> simp_all [readToken]
      simp [stopped, viewParse, propagate]
    | some nextStack =>
      have ok : result.2 = false ∧ result.1.«field:Roots» = modelRoots nextStack := by
        cases r : result.2 <;> simp [viewParse, r, h] at step ⊢
        exact step
      have growth : nextStack.length ≤ roots.length + 1 := by
        obtain ⟨tok, offset⟩ := t
        cases tok with
        | literal v =>
          simp [readToken] at h
          subst nextStack
          simp
        | not =>
          cases roots <;> simp [readToken] at h
          subst nextStack
          simp
        | binary op =>
          cases roots with
          | nil => simp [readToken] at h
          | cons l tail =>
            cases tail <;> simp [readToken] at h
            subst nextStack
            simp
      have state : result.1 = ⟨words, modelRoots nextStack⟩ :=
        by
          cases eq : result.1
          rw [eq] at sameWords
          have rootEq := ok.2
          rw [eq] at rootEq
          exact parser.mk.injEq .. |>.mpr ⟨sameWords, rootEq⟩
      simpa only [ok.1, Bool.false_eq_true, ite_false, state] using
        ih (index + 1) nextStack (by omega) (by omega)

private theorem parseLayout (words : Array lexeme) (tokens : List LocatedToken)
    (layout : words.toList = tokens.map locatedLexeme) (fits : words.size ≤ maxInt) :
    viewParse (parse words) = (tokens.foldr readToken (some [])).map modelRoots := by
  have lengths : words.size = tokens.length := by simpa using congrArg List.length layout
  unfold parse
  rw [sizeNat fits]
  simpa [lengths, modelRoots] using
    parseCorresponds words tokens layout fits words.size 0 [] (by simp) (by simp)

private theorem checkCorrect (e : Expr) :
    checkExpression (modelExpr e) =
      match e.check with
      | .ok ty => typed (Requirements.Ty.tag ty)
      | .error offset => mismatch (UInt64.ofNat offset) := by
  induction e with
  | literal v offset =>
    cases v <;> rw [checkExpression.eq_def] <;> rfl
  | not offset operand ih =>
    rw [checkExpression.eq_def]
    cases h : operand.check with
    | error err =>
      simp [modelExpr, locatedLexeme, tokenClass, expression.«field:Word», expression.«field:Left»,
        expression.«field:Right», ih, h, Expr.check, Bind.bind, Except.bind, mismatch]
    | ok ty =>
      cases ty <;> simp [modelExpr, locatedLexeme, tokenClass, expression.«field:Word»,
        expression.«field:Left», expression.«field:Right», ih, h, Expr.check, Bind.bind, Except.bind,
        typed, noDiagnostic, mismatch, Requirements.Ty.tag, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | binary op offset l r il ir =>
    rw [checkExpression.eq_def]
    cases hr : r.check <;> cases hl : l.check <;>
      simp [modelExpr, locatedLexeme, expression.«field:Word», expression.«field:Left»,
        expression.«field:Right», il, ir, hr, hl, Expr.check, Bind.bind, Except.bind, typed,
        noDiagnostic, mismatch, Requirements.Ty.tag, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    all_goals rename_i lt rt
    all_goals cases op <;> cases lt <;> cases rt <;> rfl

private theorem emitCorrect (e : Expr) (code : ByteArray) :
    (emitExpression (modelExpr e) code).data.toList = code.data.toList ++ e.instructions := by
  induction e generalizing code with
  | literal v offset =>
    cases v <;> rw [emitExpression.eq_def] <;> simp [modelExpr, leaf, locatedLexeme, tokenClass,
      expression.«field:Left», expression.«field:Word», emitWord, encode, Expr.instructions, Value.byte]
  | not offset operand ih =>
    rw [emitExpression.eq_def]
    simp [modelExpr, locatedLexeme, tokenClass, expression.«field:Left», expression.«field:Right»,
      expression.«field:Word», emitWord, encode, Expr.instructions, ih, List.append_assoc]
  | binary op offset l r il ir =>
    rw [emitExpression.eq_def]
    cases op <;> simp [modelExpr, locatedLexeme, tokenClass, expression.«field:Left», expression.«field:Right»,
      expression.«field:Word», emitWord, encode, Expr.instructions, BinOp.opcode, il, ir, List.append_assoc]

private theorem codeFitsIff (n : Nat) (repr : n ≤ maxInt) :
    codeFits (UInt64.ofNat n) = true ↔ 2 * n + 2 ≤ maxInt := by
  simp only [codeFits, decide_eq_true_eq, UInt64.le_iff_toNat_le, sizeNat repr]
  change n ≤ 4611686018427387902 ↔ _
  unfold maxInt
  omega

private theorem wordsCount {offset : Nat} {bytes : List UInt8} {words : List Word}
    (splitWords : Words offset bytes words) : words.length ≤ bytes.length := by
  induction splitWords with
  | done => simp
  | space _ _ ih => simp; omega
  | word nonempty _ _ _ ih =>
    have nonzero := List.length_pos_iff.mpr nonempty
    simp
    omega

private theorem lexedCount {words : List Word} {tokens : List LocatedToken}
    (lexed : Lexed words tokens) : words.length = tokens.length := by
  induction lexed <;> simp_all
private theorem tokenizeLayout (source : ByteArray) (fits : source.size ≤ maxInt)
    {words : List Word} {tokens : List LocatedToken}
    (splitWords : Words 0 source.data.toList words) (lexed : Lexed words tokens) :
    let scanned := tokenize source
    scanned.«field:Words».toList = tokens.map locatedLexeme ∧
      scanned.«field:Error».«field:Kind» = 0 ∧ scanned.«field:Words».size ≤ maxInt := by
  have ⟨layout, clean⟩ := tokenizeRecognized source fits _ _ splitWords lexed
  have size := congrArg List.length layout
  simp at size
  have bound := wordsCount splitWords
  rw [lexedCount lexed, ← size, Array.length_toList, ByteArray.size_data] at bound
  exact ⟨layout, by rw [clean]; rfl, Nat.le_trans bound fits⟩

private theorem wordOffsets {off : Nat} {bytes : List UInt8} {words : List Word}
    (h : Words off bytes words) : ∀ word ∈ words, word.offset ≤ off + bytes.length := by
  induction h with
  | done => simp
  | space _ _ ih =>
    intro word mem
    have := ih word mem
    simp
    omega
  | word _ _ _ _ ih =>
    intro word mem
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · simp
    · have := ih word mem
      simp
      omega

private theorem lexedOffsets {words : List Word} {tokens : List LocatedToken} {bound : Nat}
    (lexed : Lexed words tokens) (h : ∀ word ∈ words, word.offset ≤ bound) :
    ∀ t ∈ tokens, t.2 ≤ bound := by
  induction lexed with
  | done => simp
  | token _ _ ih =>
    intro t mem
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact h _ (by simp)
    · exact ih (fun w wm => h w (by simp [wm])) t mem

private theorem checkErrorOffset (e : Expr) (bound : Nat)
    (fits : ∀ t ∈ e.tokens, t.2 ≤ bound) {offset : Nat} (bad : e.check = .error offset) :
    offset ≤ bound := by
  induction e generalizing offset with
  | literal v off => simp [Expr.check] at bad
  | not off expr ih =>
    have sub (t) (h : t ∈ expr.tokens) := fits t (by simp [Expr.tokens, h])
    have root : off ≤ bound := fits (.not, off) (by simp [Expr.tokens])
    cases h : expr.check with
    | error err =>
      have eq : err = offset := by simpa [Expr.check, h, Bind.bind, Except.bind] using bad
      rw [← eq]
      exact ih sub h
    | ok ty =>
      cases ty <;> simp [Expr.check, h, Bind.bind, Except.bind, Pure.pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at bad
      omega
  | binary op off l r il ir =>
    have left (t) (h : t ∈ l.tokens) := fits t (by simp [Expr.tokens, h])
    have right (t) (h : t ∈ r.tokens) := fits t (by simp [Expr.tokens, h])
    have root : off ≤ bound := fits (.binary op, off) (by simp [Expr.tokens])
    cases hr : r.check with
    | error err =>
      have eq : err = offset := by simpa [Expr.check, hr, Bind.bind, Except.bind] using bad
      rw [← eq]
      exact ir right hr
    | ok rt =>
      cases hl : l.check with
      | error err =>
        have eq : err = offset := by simpa [Expr.check, hr, hl, Bind.bind, Except.bind] using bad
        rw [← eq]
        exact il left hl
      | ok lt =>
        simp only [Expr.check, hr, hl, Bind.bind, Except.bind] at bad
        split at bad <;> simp [Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at bad
        omega

private theorem parseSuccess (words : Array lexeme) (e : Expr)
    (layout : words.toList = e.tokens.map locatedLexeme) (fits : words.size ≤ maxInt) :
    (parse words).2 = false ∧ (parse words).1.«field:Roots» = #[modelExpr e] := by
  have p := parseLayout words e.tokens layout fits
  rw [(parseTokensIff e.tokens e).mpr rfl] at p
  cases h : (parse words).2 <;> simp [viewParse, h, modelRoots] at p ⊢
  exact p

private theorem parseReject (words : Array lexeme) (tokens : List LocatedToken)
    (layout : words.toList = tokens.map locatedLexeme) (fits : words.size ≤ maxInt)
    (invalid : ¬ ∃ e : Expr, e.tokens = tokens) :
    (parse words).2 = true ∨ UInt64.ofNat (parse words).1.«field:Roots».size ≠ 1 := by
  cases stop : (parse words).2
  · apply Or.inr
    intro one
    have eq := parseLayout words tokens layout fits
    cases h : tokens.foldr readToken (some []) with
    | none => simp [viewParse, stop, h] at eq
    | some roots =>
      simp [viewParse, stop, h] at eq
      rw [eq, modelRootsSize] at one
      have length : roots.length ≤ words.size := by
        have levels (ts : List LocatedToken) (rs out : List Expr)
            (h : ts.foldr readToken (some rs) = some out) : out.length ≤ rs.length + ts.length := by
          induction ts generalizing out with
          | nil => simp_all
          | cons t ts ih =>
            simp only [List.foldr_cons] at h
            cases hr : ts.foldr readToken (some rs) with
            | none => simp [hr, readToken] at h
            | some mid =>
              have bound := ih mid hr
              rw [hr] at h
              obtain ⟨tok, off⟩ := t
              cases tok with
              | literal v => simp [readToken] at h; subst out; simp; omega
              | not =>
                cases mid <;> simp [readToken] at h
                subst out
                simp_all
                omega
              | binary op =>
                cases mid with
                | nil => simp [readToken] at h
                | cons l tail =>
                  cases tail <;> simp [readToken] at h
                  subst out
                  simp_all
                  omega
        have len : words.size = tokens.length := by simpa using congrArg List.length layout
        simpa [len] using levels tokens [] roots h
      have len := congrArg UInt64.toNat one
      rw [sizeNat (Nat.le_trans length fits)] at len
      obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp (show roots.length = 1 from len)
      exact invalid ⟨e, (parseTokensIff tokens e).mp h⟩
  · exact Or.inl rfl

private inductive LexicalFailure : List Word → Nat → Prop where
  | first : ¬ ValidWord word → LexicalFailure (word :: rest) word.offset
  | later : ValidWord word → LexicalFailure rest offset → LexicalFailure (word :: rest) offset

private theorem firstFailure {words : List Word} {offset : Nat} (h : FirstLexError words offset) :
    LexicalFailure words offset := by
  obtain ⟨before, word, tail, rfl, rfl, earlier, invalid⟩ := h
  induction before with
  | nil => exact .first invalid
  | cons w ws ih =>
    exact .later (earlier w (by simp)) (ih (fun v mem => earlier v (by simp [mem])))

set_option maxHeartbeats 2000000 in
private theorem scanFirstFailure (source : ByteArray) (fits : source.size ≤ maxInt)
    {offset failure : Nat} {bytes : List UInt8} {words : List Word}
    (splitWords : Words offset bytes words) (bad : LexicalFailure words failure)
    (suffix : source.data.toList.drop offset = bytes) (length : offset + bytes.length = source.size)
    (prior : Array lexeme) (start : UInt64) :
    let result := finishScan (UInt64.ofNat source.size)
      («fold».countUntil scanSourceByte bytes.length (UInt64.ofNat offset)
        ⟨source, prior, ⟨start, false⟩, noDiagnostic⟩)
    result.«field:Error» = ⟨2, UInt64.ofNat failure⟩ := by
  induction splitWords generalizing prior start with
  | done => cases bad
  | @space b off tail ws space _ ih =>
    have offFit : off ≤ maxInt := by simp at length; omega
    have atByte : source[(UInt64.ofNat off).toNat]? = some b := by
      rw [sizeNat offFit, byteAtList, ← List.head?_drop, suffix]
      rfl
    have rest : source.data.toList.drop (off + 1) = tail := by
      rw [List.drop_add_one_eq_tail_drop, suffix]
      rfl
    rw [List.length_cons, «fold».countUntil,
      scanDelimiter source (UInt64.ofNat off) start prior false noDiagnostic b atByte space]
    simpa using ih bad rest (by simp at length; omega) prior start
  | @word w off tail ws nonempty nonspace boundary _ ih =>
    cases w with
    | nil => contradiction
    | cons b bs =>
      let w := b :: bs
      let next := off + w.length
      let i := UInt64.ofNat off
      let j := UInt64.ofNat next
      have iFit : off ≤ maxInt := by simp at length; omega
      have jFit : next ≤ maxInt := by simp [next, w] at length ⊢; omega
      have il : i.toNat = off := sizeNat iFit
      have jl : j.toNat = next := sizeNat jFit
      have restBytes : source.data.toList.drop next = tail := by
        dsimp only [next]
        rw [← List.drop_drop, suffix, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
      let slice := source.extract i.toNat j.toNat
      have sliceBytes : slice.data.toList = w := by
        dsimp only [slice]
        rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop, il, jl, suffix]
        have width : next - off = w.length := by simp [next]
        rw [width, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      have sliceFits : slice.size ≤ maxInt := by
        simpa [slice, ByteArray.size_extract] using
          show min j.toNat source.size - i.toNat ≤ maxInt by omega
      let old : lexer := ⟨source, prior, ⟨i, true⟩, noDiagnostic⟩
      have scan := scanWordStart source i start prior noDiagnostic b bs tail
        (by simpa only [il] using suffix) fits nonspace
      rw [List.length_append, scanFoldAppend, scan]
      simp only [Bool.false_eq_true, ite_false]
      rw [← UInt64.ofNat_add]
      change (finishScan (UInt64.ofNat source.size) («fold».countUntil scanSourceByte tail.length j old)).«field:Error» = _
      cases bad with
      | first invalid =>
        have rejected : (classify slice).«field:Kind» = 0 := by
          by_cases h : (classify slice).«field:Kind» = 0
          · exact h
          · obtain ⟨tok, valid⟩ := classifyValid slice sliceFits h
            rw [sliceBytes] at valid
            exact False.elim (invalid ⟨tok, valid⟩)
        have closing : closeWord j old ⟨i, false⟩ = lexError old 2 i := by
          simp [closeWord, old, slice, rejected]
        cases tail with
        | nil =>
          have endAt : UInt64.ofNat source.size = j := by
            congr 1
            simp [next, w] at length ⊢
            omega
          rw [endAt]
          change (closeWord j old ⟨i, false⟩).1.«field:Error» = _
          rw [closing]
          rfl
        | cons d ds =>
          have atByte : source[j.toNat]? = some d := by
            rw [jl, byteAtList, ← List.head?_drop, restBytes]
            rfl
          have step : scanSourceByte j old = lexError old 2 i := by
            rw [show old = ⟨source, prior, ⟨i, true⟩, noDiagnostic⟩ from rfl,
              scanDelimiter source j i prior true noDiagnostic d atByte (boundary d rfl)]
            exact closing
          simp [«fold».countUntil, step, finishScan, lexError]
          rfl
      | later valid remaining =>
        obtain ⟨tok, recognized⟩ := valid
        let word := locatedLexeme (tok, off)
        let closed : lexer := ⟨source, prior.push word, ⟨i, false⟩, noDiagnostic⟩
        have closing : closeWord j old ⟨i, false⟩ = (closed, false) :=
          closeRecognizedWord source i j prior noDiagnostic ⟨i, true⟩ tok (by change Recognizes slice.data.toList tok; rw [sliceBytes]; exact recognized)
        have advance :
            finishScan (UInt64.ofNat source.size) («fold».countUntil scanSourceByte tail.length j old) =
            finishScan (UInt64.ofNat source.size) («fold».countUntil scanSourceByte tail.length j closed) := by
          cases tail with
          | nil =>
            have endAt : UInt64.ofNat source.size = j := by
              congr 1
              simp [next, w] at length ⊢
              omega
            simp [«fold».countUntil, endAt, finishScan, old, closing, closed]
          | cons d ds =>
            have atByte : source[j.toNat]? = some d := by
              rw [jl, byteAtList, ← List.head?_drop, restBytes]
              rfl
            have space := boundary d rfl
            rw [List.length_cons, «fold».countUntil, «fold».countUntil,
              show scanSourceByte j old = _ from scanDelimiter source j i prior true noDiagnostic d atByte space,
              show scanSourceByte j closed = (closed, false) from
                scanDelimiter source j i (prior.push word) false noDiagnostic d atByte space]
            rw [show closeWord j ⟨source, prior, ⟨i, true⟩, noDiagnostic⟩ ⟨i, false⟩ =
              (closed, false) from closing]
            rfl
        rw [advance]
        exact ih remaining restBytes (by simp at length ⊢; omega) (prior.push word) i

private theorem tokenizeFirstFailure (source : ByteArray) (fits : source.size ≤ maxInt)
    {words : List Word} {offset : Nat} (splitWords : Words 0 source.data.toList words)
    (first : FirstLexError words offset) :
    (tokenize source).«field:Error» = ⟨2, UInt64.ofNat offset⟩ := by
  have result := scanFirstFailure source fits splitWords (firstFailure first) (by simp)
    (by simp [ByteArray.size_data]) #[] 0
  unfold tokenize
  rw [sizeNat fits]
  simpa [finishScan, Bool.or_eq_true] using result

private theorem compilationCorrect : Requirements.compilationConforms compileResult := by
  intro source fits
  refine ⟨outcomeExists _, ?_⟩
  intro outcome specified
  cases specified
  case lexical words offset splitWords first =>
    have bad := tokenizeFirstFailure source fits splitWords first
    have representable : offset ≤ maxInt := by
      obtain ⟨before, word, tail, rfl, rfl, _, _⟩ := first
      have := wordOffsets splitWords word (by simp)
      simp at this
      omega
    simp [compileResult, compile, bad, failed, Requirements.observesCompilation,
      Requirements.Diagnostic.tag, sizeNat representable]
  case «syntax» splitWords lexed invalid =>
    have ⟨layout, clean, bound⟩ := tokenizeLayout source fits splitWords lexed
    have reject := parseReject _ _ layout bound invalid
    simp [compileResult, compile, clean, reject, failed, Requirements.observesCompilation,
      Requirements.Diagnostic.tag, sizeNat fits]
  case typeMismatch words offset e splitWords lexed bad =>
    have ⟨layout, clean, bound⟩ := tokenizeLayout source fits splitWords lexed
    have ⟨stop, roots⟩ := parseSuccess _ e layout bound
    have chk := checkCorrect e
    rw [bad] at chk
    have offsets := lexedOffsets lexed (wordOffsets splitWords)
    have representable : offset ≤ maxInt := by
      have := checkErrorOffset e source.data.toList.length (by simpa using offsets) bad
      simp at this
      omega
    simp [compileResult, compile, clean, stop, roots, chk, mismatch, failed,
      Requirements.observesCompilation, Requirements.Diagnostic.tag, sizeNat representable]
  case codeTooLarge words ty e splitWords lexed good large =>
    have ⟨layout, clean, bound⟩ := tokenizeLayout source fits splitWords lexed
    have ⟨stop, roots⟩ := parseSuccess _ e layout bound
    have chk := checkCorrect e
    rw [good] at chk
    have count : (tokenize source).«field:Words».size = e.tokens.length := by
      simpa using congrArg List.length layout
    have tooLarge : codeFits (UInt64.ofNat (tokenize source).«field:Words».size) = false := by
      cases h : codeFits (UInt64.ofNat (tokenize source).«field:Words».size)
      · rfl
      · have := (codeFitsIff _ bound).mp h
        omega
    simp [compileResult, compile, clean, stop, roots, chk, typed, noDiagnostic, tooLarge, failed,
      Requirements.observesCompilation, Requirements.Diagnostic.tag, sizeNat fits]
  case success words ty e splitWords lexed good small =>
    have ⟨layout, clean, bound⟩ := tokenizeLayout source fits splitWords lexed
    have ⟨stop, roots⟩ := parseSuccess _ e layout bound
    have chk := checkCorrect e
    rw [good] at chk
    have count : (tokenize source).«field:Words».size = e.tokens.length := by
      simpa using congrArg List.length layout
    have enough := (codeFitsIff _ bound).mpr (by omega)
    simp [compileResult, compile, clean, stop, roots, chk, typed, noDiagnostic, enough,
      Requirements.observesCompilation, emit, emitCorrect, Expr.bytecode, List.append_assoc]

theorem «all» : Laws.«all» :=
  ⟨compilationCorrect, stepCorrect, executionCorrect, preservesMeaning compilationCorrect⟩

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/stack-machine-compiler».Proofs
