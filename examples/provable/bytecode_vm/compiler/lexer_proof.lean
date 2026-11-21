import bytecode_vm.compiler.lexer_spec

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.LexerProofs

open LexerSpec LexerModel

private abbrev Word := GoTypes.Int

private def index (n : Nat) : Word := .ofNat n

private theorem wordInt (n : Nat) (h : (n : Int) < 2 ^ (GoTypes.WordBits - 1)) :
    (index n).toInt = n := by
  change (.ofInt (n : Int) : Word).toInt = n
  first
  | exact Int64.toInt_ofInt_of_le (by omega) h
  | exact Int32.toInt_ofInt_of_le (by omega) h

private theorem smallWord (n : Nat) (h : n ≤ 258) : (index n).toInt = n :=
  wordInt n (by unfold GoTypes.WordBits; omega)

private theorem wordAdd (a b : Nat) : index a + index b = index (a + b) := by
  change (.ofInt (a : Int) : Word) + .ofInt (b : Int) = .ofInt ((a + b : Nat) : Int)
  rw [Int.natCast_add]
  first | rw [← Int64.ofInt_add] | rw [← Int32.ofInt_add]

private theorem wordLt {a b : Word} : a < b ↔ a.toInt < b.toInt := by
  first | exact Int64.lt_iff_toInt_lt | exact Int32.lt_iff_toInt_lt

private theorem wordEq {a b : Word} : a = b ↔ a.toInt = b.toInt := by
  first | exact Int64.toInt_inj.symm | exact Int32.toInt_inj.symm

private theorem spaces (b : UInt8) : isSpace b = decide (space b) := by
  by_cases h1 : b = 32 <;> by_cases h2 : b = 9 <;>
    by_cases h3 : b = 13 <;> by_cases h4 : b = 10 <;> simp [isSpace, space, h1, h2, h3, h4]

private theorem digits (b : UInt8) : isDigit b = decide (digit b) := by
  by_cases lo : 48 ≤ b <;> by_cases hi : b ≤ 57 <;> simp [isDigit, digit, lo, hi]

private theorem pair (a b x y : UInt8) : matchPair a b x y = decide ((a, b) = (x, y)) := by
  by_cases h1 : a = x <;> by_cases h2 : b = y <;> simp [matchPair, h1, h2]

private theorem triple (a b c x y z : UInt8) :
    matchTriple a b c x y z = decide ((a, b, c) = (x, y, z)) := by
  by_cases h1 : a = x <;> by_cases h2 : b = y <;> by_cases h3 : c = z <;>
    simp [matchTriple, pair, h1, h2, h3]

private theorem twoBytes (a b : UInt8) : classifyTwo a b = word [a, b] := by
  by_cases h1 : (a, b) = (101, 113) <;> by_cases h2 : (a, b) = (108, 116) <;>
    by_cases h3 : a = 48 <;> by_cases h4 : digit a <;> by_cases h5 : digit b <;>
      simp [classifyTwo, word, pair, Prod.mk.injEq, digits, h1, h2, h3, h4, h5]

private theorem threeBytes (a b c : UInt8) : classifyThree a b c = word [a, b, c] := by
  by_cases h1 : (a, b, c) = (97, 100, 100) <;>
    by_cases h2 : (a, b, c) = (115, 117, 98) <;>
    by_cases h3 : (a, b, c) = (97, 110, 100) <;>
    by_cases h4 : (a, b, c) = (110, 111, 116) <;>
    by_cases h5 : a = 48 <;> by_cases h6 : digit a <;>
    by_cases h7 : digit b <;> by_cases h8 : digit c <;>
      simp [classifyThree, word, triple, Prod.mk.injEq, digits, h1, h2, h3, h4, h5, h6, h7, h8,
        digitValue]

private theorem addOne (n : Nat) : index n + (.ofInt 1 : Word) = index (n + 1) := wordAdd n 1
private theorem addTwo (n : Nat) : index n + (.ofInt 2 : Word) = index (n + 2) := wordAdd n 2
private theorem addThree (n : Nat) : index n + (.ofInt 3 : Word) = index (n + 3) := wordAdd n 3
private theorem addFour (n : Nat) : index n + (.ofInt 4 : Word) = index (n + 4) := wordAdd n 4
private theorem classifySpan (source : List UInt8) (start width : Nat) (cap : source.length ≤ 256)
    (bounds : start + width ≤ source.length) :
    classify source (index start) (index width) = some (word ((source.drop start).take width)) := by
  generalize spanDef : (source.drop start).take width = span
  have size : span.length = width := by
    simp [← spanDef, Nat.min_eq_left (show width ≤ source.length - start by omega)]
  have read (i : Nat) (within : i < width) : source[start + i]? = span[i]? := by
    rw [← spanDef, List.getElem?_take_of_lt within, List.getElem?_drop]
  have r0 (h : 0 < width) : source[start]? = span[0]? := by simpa using read 0 h
  have nStart : ¬ (index start).toInt < 0 := by
    rw [smallWord start (by omega)]
    omega
  have nAt (i : Nat) (h : i < width) : ¬ (index (start+i)).toInt < 0 := by
    rw [smallWord _ (by omega)]
    omega
  have rStart (h : 0 < width) :
      source[(index start).toInt.toNat]? = span[0]? := by
    rw [smallWord _ (by omega), Int.toNat_natCast, r0 h]
  have rAt (i : Nat) (h : i < width) :
      source[(index (start+i)).toInt.toNat]? = span[i]? := by
    rw [smallWord _ (by omega), Int.toNat_natCast, read i h]
  have eqWidth (n : Nat) (hn : n ≤ 5) : index width = index n ↔ width = n := by
    rw [wordEq, smallWord width (by omega), smallWord n (by omega)]
    omega
  have e1 : (index width = (.ofInt 1 : Word)) = (width = 1) := propext (eqWidth 1 (by decide))
  have e2 : (index width = (.ofInt 2 : Word)) = (width = 2) := propext (eqWidth 2 (by decide))
  have e3 : (index width = (.ofInt 3 : Word)) = (width = 3) := propext (eqWidth 3 (by decide))
  have e4 : (index width = (.ofInt 4 : Word)) = (width = 4) := propext (eqWidth 4 (by decide))
  have e5 : (index width = (.ofInt 5 : Word)) = (width = 5) := propext (eqWidth 5 (by decide))
  simp only [classify, e1, e2, e3, e4, e5]
  simp only [decide_eq_true_eq, addOne, addTwo, addThree, addFour]
  rcases span with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
  · have w : width = 0 := by simpa using size.symm
    simp [w, word]
  · have w : width = 1 := by simpa using size.symm
    simp only [w, ite_true]
    simp only [nStart, ite_false, rStart (by omega)]
    by_cases d : digit a <;> simp [digits, word, d]
  · have w : width = 2 := by simpa using size.symm
    simp only [w, show (2 : Nat) ≠ 1 by decide, ite_true, ite_false]
    simp only [nStart, nAt 1 (by omega), ite_false, rStart (by omega), rAt 1 (by omega)]
    simp [twoBytes]
  · have w : width = 3 := by simpa using size.symm
    simp only [w, show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, ite_true, ite_false]
    simp only [nStart, nAt 1 (by omega), nAt 2 (by omega), ite_false, rStart (by omega), rAt 1 (by omega), rAt 2 (by omega)]
    simp [threeBytes]
  · have w : width = 4 := by simpa using size.symm
    simp only [w, show (4 : Nat) ≠ 1 by decide, show (4 : Nat) ≠ 2 by decide,
      show (4 : Nat) ≠ 3 by decide, ite_true, ite_false]
    simp only [nStart, nAt 1 (by omega), nAt 2 (by omega), nAt 3 (by omega), ite_false, rStart (by omega), rAt 1 (by omega), rAt 2 (by omega), rAt 3 (by omega)]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, bind, Option.bind, pure, pair, word,
      decide_eq_true_eq]
    change (if (a, b) = (116, 114) then
      if (c, d) = (117, 101) then some (2, 1) else some (0, 0) else some (0, 0)) = _
    have eq : ((a, b, c, d) = (116, 114, 117, 101)) ↔
        (a, b) = (116, 114) ∧ (c, d) = (117, 101) := by simp [and_assoc]
    simp only [eq]
    by_cases head : (a, b) = (116, 114) <;> by_cases tail : (c, d) = (117, 101) <;>
      simp only [head, tail, ite_true, ite_false, true_and, false_and, and_false]
  · cases rest with
    | nil =>
      have w : width = 5 := by simpa using size.symm
      simp only [w, show (5 : Nat) ≠ 1 by decide, show (5 : Nat) ≠ 2 by decide,
        show (5 : Nat) ≠ 3 by decide, show (5 : Nat) ≠ 4 by decide, ite_true, ite_false]
      simp only [nStart, nAt 1 (by omega), nAt 2 (by omega), nAt 3 (by omega), nAt 4 (by omega), ite_false, rStart (by omega), rAt 1 (by omega), rAt 2 (by omega), rAt 3 (by omega), rAt 4 (by omega)]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, bind, Option.bind, pure, pair, triple,
        word, decide_eq_true_eq]
      change (if (a, b) = (102, 97) then
        if (c, d, e) = (108, 115, 101) then some (2, 0) else some (0, 0) else some (0, 0)) = _
      have eq : ((a, b, c, d, e) = (102, 97, 108, 115, 101)) ↔
          (a, b) = (102, 97) ∧ (c, d, e) = (108, 115, 101) := by simp [and_assoc]
      simp only [eq]
      by_cases head : (a, b) = (102, 97) <;> by_cases tail : (c, d, e) = (108, 115, 101) <;>
        simp only [head, tail, ite_true, ite_false, true_and, false_and, and_false]
    | cons f rest =>
      simp only [List.length_cons] at size
      have w1 : width ≠ 1 := by omega
      have w2 : width ≠ 2 := by omega
      have w3 : width ≠ 3 := by omega
      have w4 : width ≠ 4 := by omega
      have w5 : width ≠ 5 := by omega
      simp [w1, w2, w3, w4, w5, word]

private theorem fieldNil (project : Token → α) (zero : α) :
    field project zero [] = Vector.replicate 32 zero := by
  apply Vector.ext
  simp [field]

private theorem fieldAppend (project : Token → α) (zero : α) (out : List Token) (t : Token) :
    (field project zero out).setIfInBounds out.length (project t) =
      field project zero (out ++ [t]) := by
  apply Vector.ext
  intro i within
  rw [Vector.getElem_setIfInBounds]
  by_cases eq : out.length = i
  · simp [eq, field]
  · by_cases old : i < out.length
    · simp [eq, field, List.getElem?_append_left old]
    · have past : [t].length ≤ i - out.length := by simp; omega
      simp [eq, field, List.getElem?_append_right (by omega : out.length ≤ i),
        List.getElem?_eq_none past, List.getElem?_eq_none (by omega : out.length ≤ i)]

private theorem castByte (n : Nat) (h : n ≤ 258) : (Int8.ofInt (index n).toInt).toUInt8 = UInt8.ofNat n := by
  rw [smallWord n h]
  rfl

private theorem castShort (n : Nat) (h : n ≤ 258) : (Int16.ofInt (index n).toInt).toUInt16 = UInt16.ofNat n := by
  rw [smallWord n h]
  rfl

private theorem atNat (n : Nat) (h : n ≤ 258) : (index n).toInt.toNat = n := by
  rw [smallWord n h, Int.toNat_natCast]

private theorem notNeg (n : Nat) (h : n ≤ 258) : ¬ (index n).toInt < 0 := by
  rw [smallWord n h]
  omega

private theorem idxLt (a b : Nat) (ha : a ≤ 258) (hb : b ≤ 258) :
    index a < index b ↔ a < b := by
  rw [wordLt, smallWord a ha, smallWord b hb]
  omega

private theorem idxEq (a b : Nat) (ha : a ≤ 258) (hb : b ≤ 258) :
    index a = index b ↔ a = b := by
  rw [wordEq, smallWord a ha, smallWord b hb]
  omega

private theorem readVec (xs : Vector α 32) (i : Nat) (bound : i < 32) :
    xs.toArray[i]? = some xs[i] := by
  rw [Array.getElem?_eq_getElem (by simpa using bound)]
  rfl

private theorem zeroIndex : index 0 = (.ofInt 0 : Word) := rfl

private abbrev kinds (out : List Token) := field Token.kind 0 out
private abbrev values (out : List Token) := field Token.value 0 out
private abbrev offsets (out : List Token) := field (UInt16.ofNat ∘ Token.start) 0 out

/-- The expected Go loop state encodes the complete tokens and the current lexeme span. -/
private def carried (i start width : Nat) (out : List Token) :
    Word × Word × Word × Word × Vector UInt8 32 × Vector UInt8 32 × Vector UInt16 32 :=
  (index out.length, index start, index width, index i, kinds out, values out, offsets out)

private theorem loopDone (source : List UInt8) (cap : source.length ≤ 256)
    (i start width : Nat) (out : List Token) (bound : out.length ≤ 32) :
    tokenize.«v9_loop» source (index source.length) (index (source.length + 1))
      0 (carried i start width out) = some (result source.length (.ok out)) := by
  simp only [tokenize.«v9_loop», carried, result, castByte out.length (by omega),
    castShort source.length (by omega)]
  rfl

private theorem idxZero (n : Nat) (h : n ≤ 258) : index n = (.ofInt 0 : Word) ↔ n = 0 :=
  idxEq n 0 h (by decide)

private theorem idxCapacity (n : Nat) (h : n ≤ 258) : index n = (.ofInt 32 : Word) ↔ n = 32 :=
  idxEq n 32 h (by decide)

private theorem emptyEncoding :
    LexerModel.encode 0 [] =
      ⟨Vector.replicate 32 0, Vector.replicate 32 0, Vector.replicate 32 0, 0, 0⟩ := by
  simp [LexerModel.encode, fieldNil]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
private theorem scanEmpty (source : List UInt8) (cap : source.length ≤ 256)
    (start width : Nat) (out : List Token) (span : start + width ≤ source.length)
    (bound : out.length ≤ 32) :
    tokenize.«v9_loop» source (index source.length) (index (source.length + 1))
      1 (carried source.length start width out) =
        some (result source.length (finish source start width out)) := by
  have limit : ¬ index source.length < index source.length := by
    rw [idxLt _ _ (by omega) (by omega)]
    omega
  have z := idxZero width (by omega)
  have c := idxCapacity out.length (by omega)
  have cast := castShort start (by omega)
  rw [tokenize.«v9_loop».eq_2]
  by_cases empty : width = 0
  · subst width
    simp only [carried, limit, z, decide_eq_true_eq, ite_false, addOne, ite_true,
      finish, Nat.zero_eq, loopDone]
    exact loopDone source cap (source.length+1) start 0 out bound
  · rcases meaning : word ((source.drop start).take width) with ⟨kind, value⟩
    have classified := classifySpan source start width cap span
    rw [meaning] at classified
    by_cases invalid : kind = 0
    · have inv : kind = UInt8.ofNat 0 := invalid
      simp only [carried, limit, z, decide_eq_true_eq, empty, ite_false,
        classified, bind, Option.bind, Prod.fst, Prod.snd, invalid, ite_true, finish, meaning, result,
        inv, cast, emptyEncoding]
      rfl
    · have inv : kind ≠ UInt8.ofNat 0 := invalid
      simp only [carried, limit, z, decide_eq_true_eq, empty, ite_false,
        classified, bind, Option.bind, inv, c, finish, meaning, invalid]
      by_cases full : out.length = 32
      · simp only [carried, limit, z, decide_eq_true_eq, empty, ite_false,
          classified, bind, Option.bind, full, ite_true, finish, meaning, result, cast, emptyEncoding]
        rfl
      · have room : out.length < 32 := by omega
        let t : Token := ⟨kind, value, start⟩
        have newBound : (out ++ [t]).length ≤ 32 := by
          simp
          omega
        have kindWrite : (kinds out).setIfInBounds out.length kind = kinds (out ++ [t]) :=
          fieldAppend Token.kind 0 out t
        have valueWrite : (values out).setIfInBounds out.length value = values (out ++ [t]) :=
          fieldAppend Token.value 0 out t
        have offsetWrite : (offsets out).setIfInBounds out.length (UInt16.ofNat start) = offsets (out ++ [t]) :=
          fieldAppend (UInt16.ofNat ∘ Token.start) 0 out t
        simp only [carried, limit, z, decide_eq_true_eq, empty, ite_false,
          classified, bind, Option.bind, invalid, c, full, addOne, cast, atNat out.length (by omega),
          notNeg out.length (by omega), readVec (kinds out) out.length room, readVec (values out) out.length room,
          readVec (offsets out) out.length room, kindWrite, valueWrite, offsetWrite, finish, meaning]
        simpa only [carried, t, List.length_append, List.length_singleton, zeroIndex] using
          loopDone source cap (source.length+1) start 0 (out ++ [t]) newBound

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- Each real byte consumes one iteration. The additional iteration flushes the final lexeme. -/
private theorem scanLoop (source : List UInt8) (cap : source.length ≤ 256)
    (remaining : List UInt8) (i start width : Nat) (out : List Token)
    (tail : source.drop i = remaining) (within : i + remaining.length = source.length)
    (span : start + width ≤ i) (pending : width = 0 ∨ start + width = i)
    (bound : out.length ≤ 32) :
    tokenize.«v9_loop» source (index source.length) (index (source.length + 1))
      (remaining.length+1) (carried i start width out) =
        some (result source.length (scan source remaining i start width out)) := by
  induction remaining generalizing i start width out with
  | nil =>
    have done : i = source.length := by simpa using within
    subst i
    exact scanEmpty source cap start width out span bound
  | cons b rest ih =>
    rw [List.length_cons] at within ⊢
    have nextWithin : i + 1 + rest.length = source.length := by omega
    have nextTail : source.drop (i+1) = rest := by
      rw [← List.drop_drop, tail]
      rfl
    have firstByte : source[i]? = some b := by
      have read := congrArg (fun xs : List UInt8 => xs[0]?) tail
      simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using read
    have read := idxLt i source.length (by omega) (by omega)
    have inSource : index i < index source.length := read.mpr (by omega)
    have z := idxZero width (by omega)
    rw [tokenize.«v9_loop».eq_2]
    simp only [carried, decide_eq_true_eq, inSource, ite_true, notNeg i (by omega),
      atNat i (by omega), ite_false, firstByte, bind, Option.bind, spaces, scan]
    by_cases separator : space b
    · simp only [separator, ite_true, z]
      by_cases empty : width = 0
      · subst width
        simp only [ite_true, addOne, finish, Except.bind]
        exact ih (i+1) start 0 out nextTail nextWithin (by omega) (Or.inl rfl) bound
      · simp only [empty, ite_false]
        rcases meaning : word ((source.drop start).take width) with ⟨kind, value⟩
        have classified := classifySpan source start width cap (by omega)
        rw [meaning] at classified
        simp only [classified, bind, Option.bind, decide_eq_true_eq, idxCapacity out.length (by omega), finish,
          empty, ite_false, meaning]
        by_cases invalid : kind = 0
        · have inv : kind = UInt8.ofNat 0 := invalid
          simp only [invalid, inv, ite_true, Except.bind, castShort start (by omega), result, emptyEncoding]
          rfl
        · have inv : kind ≠ UInt8.ofNat 0 := invalid
          simp only [invalid, inv, ite_false]
          by_cases full : out.length = 32
          · simp only [full, ite_true, Except.bind, castShort start (by omega), result, emptyEncoding]
            rfl
          · have room : out.length < 32 := by omega
            let t : Token := ⟨kind, value, start⟩
            have newBound : (out ++ [t]).length ≤ 32 := by
              simp
              omega
            have kindWrite : (kinds out).setIfInBounds out.length kind = kinds (out ++ [t]) :=
              fieldAppend Token.kind 0 out t
            have valueWrite : (values out).setIfInBounds out.length value = values (out ++ [t]) :=
              fieldAppend Token.value 0 out t
            have offsetWrite : (offsets out).setIfInBounds out.length (UInt16.ofNat start) = offsets (out ++ [t]) :=
              fieldAppend (UInt16.ofNat ∘ Token.start) 0 out t
            simp only [full, ite_false, notNeg out.length (by omega), atNat out.length (by omega),
              readVec (kinds out) out.length room, readVec (values out) out.length room, readVec (offsets out) out.length room,
              castShort start (by omega), bind, Option.bind, Except.bind, addOne, kindWrite, valueWrite, offsetWrite]
            simpa only [carried, t, List.length_append, List.length_singleton, zeroIndex] using
              ih (i+1) start 0 (out ++ [t]) nextTail nextWithin (by omega) (Or.inl rfl) newBound
    · simp only [separator, ite_false, z, addOne]
      by_cases empty : width = 0
      · simp only [empty, decide_true, ite_true]
        simpa only [empty, carried] using
          ih (i+1) i (width+1) out nextTail nextWithin (by omega) (Or.inr (by omega)) bound
      · simp only [empty, ite_false]
        exact ih (i+1) start (width+1) out nextTail nextWithin (by omega) (Or.inr (by omega)) bound

theorem tokenizeAgrees : LexerModel.Agrees := by
  intro source fits
  have endValue : (index source.length).toInt = source.length := wordInt _ fits
  have maxValue : ((.ofInt 256 : Word).toInt) = 256 := by decide
  have tooLong : (.ofInt 256 : Word) < index source.length ↔ source.length > 256 := by
    rw [wordLt, endValue, maxValue]
    omega
  unfold tokenize
  change (if decide ((.ofInt 256 : Word) < index source.length) = true then _ else _) = _
  simp only [decide_eq_true_eq, tooLong, lex]
  by_cases long : source.length > 256
  · simp only [long, ite_true, result, emptyEncoding]
    rfl
  · have cap : source.length ≤ 256 := by omega
    simp only [long, ite_false]
    change tokenize.«v9_loop» source (index source.length) (index source.length + (.ofInt 1 : Word))
      (((index source.length + (.ofInt 1 : Word)).toInt - (.ofInt 0 : Word).toInt).toNat) _ = _
    simp only [addOne, atNat (source.length+1) (by omega),
      show ((.ofInt 0 : Word).toInt) = 0 by decide, Int.sub_zero]
    simpa only [carried, List.length_nil, zeroIndex, fieldNil,
        show UInt8.ofNat 0 = (0 : UInt8) by rfl, show UInt16.ofNat 0 = (0 : UInt16) by rfl] using
      scanLoop source cap source 0 0 0 [] (by simp) (by simp) (by simp) (Or.inl rfl) (by simp)

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.LexerProofs
