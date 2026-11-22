import bytecode_vm.compiler.layout
import bytecode_vm.compiler.parse_grammar
import bytecode_vm.compiler.parse_proof

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Parser

open Spec LexerSpec

private def forestNodes : List Expr → List Node
  | [] => []
  | e :: rest =>
    let preceding := forestNodes rest
    preceding ++ e.nodesFrom preceding.length

private def rootIndices : List Expr → List Nat
  | [] => []
  | e :: rest => rootIndices rest ++ [(forestNodes rest).length + e.nodeCount - 1]

@[simp] private theorem rootLength (trees : List Expr) :
    (rootIndices trees).length = trees.length := by
  induction trees <;> simp [rootIndices, *]

private theorem forestSize (trees : List Expr) : trees.length ≤ (forestNodes trees).length := by
  induction trees with
  | nil => decide
  | cons expr rest ih =>
    have positive := expr.positive
    simp [forestNodes]
    omega

private def Buffer [OfNat α 0] (vector : Vector α 32) (xs : List α) : Prop :=
  ∀ i, i < 32 → vector.getD i 0 = xs[i]?.getD 0

private theorem getAt [OfNat α 0] (vector : Vector α 32) {i : Nat} (within : i < 32) :
    vector.getD i 0 = vector[i] := by
  simp [Vector.getD, within]

private theorem writeAt [OfNat α 0] (vector : Vector α 32) (i j : Nat) (value : α)
    (within : i < 32) :
    (vector.setIfInBounds j value).getD i 0 = if j = i then value else vector.getD i 0 := by
  rw [getAt _ within, getAt _ within, Vector.getElem_setIfInBounds]

private theorem appendCell [OfNat α 0] (vector : Vector α 32) (xs : List α) (value : α)
    (before : Buffer vector xs) :
    Buffer (vector.setIfInBounds xs.length value) (xs ++ [value]) := by
  intro i within
  rw [writeAt _ _ _ _ within]
  by_cases equal : xs.length = i
  · subst i
    simp
  · rw [ite_eq_right equal, before i within]
    by_cases old : i < xs.length
    · rw [List.getElem?_append_left old]
    · have past : (xs ++ [value]).length ≤ i := by simp; omega
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none past]

private theorem appendZero [OfNat α 0] (vector : Vector α 32) (xs : List α)
    (before : Buffer vector xs) : Buffer vector (xs ++ [0]) := by
  intro i within
  rw [before i within]
  by_cases old : i < xs.length
  · rw [List.getElem?_append_left old]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_append_right (by omega)]
    cases (i - xs.length) <;> rfl

private def Roots (array : Vector UInt8 32) (indices : List Nat) : Prop :=
  ∀ i (within : i < indices.length), (array.getD i 0).toNat = indices[i]

private theorem replaceRoots (array : Vector UInt8 32) (saved removed : List Nat)
    (old : Roots array (saved ++ removed)) (next : Nat) (room : saved.length < 32) (fits : next < 256) :
    Roots (array.setIfInBounds saved.length (UInt8.ofNat next)) (saved ++ [next]) := by
  intro i within
  have inArray : i < 32 := by simp at within; omega
  rw [writeAt _ _ _ _ inArray]
  by_cases earlier : i < saved.length
  · rw [ite_eq_right (by omega), old i (by simp; omega), List.getElem_append_left earlier,
      List.getElem_append_left earlier]
  · have last : i = saved.length := by simp at within; omega
    subst i
    simp [List.getElem_append_right, Nat.mod_eq_of_lt fits]

private structure Snapshot (arena : Arena) (trees : List Expr) : Prop where
  kinds : Buffer arena.kinds ((forestNodes trees).map Node.kind)
  values : Buffer arena.values ((forestNodes trees).map Node.value)
  offsets : Buffer arena.offsets ((forestNodes trees).map (UInt16.ofNat ∘ Node.start))
  left : Buffer arena.left ((forestNodes trees).map (UInt8.ofNat ∘ Node.left))
  right : Buffer arena.right ((forestNodes trees).map (UInt8.ofNat ∘ Node.right))
  roots : Roots arena.roots (rootIndices trees)

private theorem initial : Snapshot {} [] := by
  constructor <;> simp [Buffer, Roots, forestNodes, rootIndices]
  all_goals intro i within; rw [getAt _ within]; simp

private theorem rootAtTop (arena : Arena) (expr : Expr) (trees : List Expr)
    (before : Snapshot arena (expr :: trees)) :
    (arena.roots.getD trees.length 0).toNat = (forestNodes trees).length + expr.nodeCount - 1 := by
  have atTop := before.roots trees.length (by simp)
  simpa [rootIndices, List.getElem_append_right] using atTop

private theorem rootByte (arena : Arena) (expr : Expr) (trees : List Expr)
    (before : Snapshot arena (expr :: trees)) :
    arena.roots.getD trees.length 0 = UInt8.ofNat ((forestNodes trees).length + expr.nodeCount - 1) := by
  rw [← rootAtTop arena expr trees before, UInt8.ofNat_toNat]

private def inputToken (input : tokens) (i : Nat) : Token :=
  ⟨input.«field:Kind».getD i 0, input.«field:Value».getD i 0,
    (input.«field:Start».getD i 0).toNat⟩

private theorem grows (input : tokens) (i reversed : Nat) (arena : Arena) (before after : List Expr)
    (snapshot : Snapshot arena before) (written : (forestNodes before).length = i) (room : i < 32)
    (step : Grammar.pushTree (inputToken input reversed) before = some after) :
    Snapshot (insert input i reversed before.length
      (operandCount (input.«field:Kind».getD reversed 0)) arena) after ∧
      (forestNodes after).length = i + 1 := by
  let tok := inputToken input reversed
  change Grammar.pushTree tok before = some after at step
  have sameKind : input.«field:Kind».getD reversed 0 = tok.kind := rfl
  have sameValue : input.«field:Value».getD reversed 0 = tok.value := rfl
  have sameStart : input.«field:Start».getD reversed 0 = UInt16.ofNat tok.start := by
    exact UInt16.ofNat_toNat.symm
  have previous := forestSize before
  cases decoded : Grammar.form tok with
  | none => simp [Grammar.pushTree, decoded] at step
  | some f =>
    have canonical := Grammar.token_of_form decoded
    rw [← canonical] at sameKind sameValue
    cases f with
    | integer value =>
      simp [Grammar.pushTree, decoded] at step
      subst after
      have roots := replaceRoots arena.roots (rootIndices before) [] (by simpa using snapshot.roots)
        i (by simpa only [rootLength] using (show before.length < 32 by omega)) (by omega)
      refine ⟨?_, by simp [forestNodes, written, Expr.nodeCount]⟩
      constructor
      · simpa [insert, sameKind, Grammar.token, forestNodes, Expr.nodesFrom, written] using
          appendCell arena.kinds ((forestNodes before).map Node.kind) 1 snapshot.kinds
      · simpa [insert, sameValue, Grammar.token, forestNodes, Expr.nodesFrom, written] using
          appendCell arena.values ((forestNodes before).map Node.value) value snapshot.values
      · simpa [insert, sameStart, forestNodes, Expr.nodesFrom, written] using
          appendCell arena.offsets ((forestNodes before).map (UInt16.ofNat ∘ Node.start))
            (UInt16.ofNat tok.start) snapshot.offsets
      · simpa [insert, sameKind, Grammar.token, operandCount, forestNodes, Expr.nodesFrom] using
          appendZero arena.left ((forestNodes before).map (UInt8.ofNat ∘ Node.left)) snapshot.left
      · simpa [insert, sameKind, Grammar.token, operandCount, forestNodes, Expr.nodesFrom] using
          appendZero arena.right ((forestNodes before).map (UInt8.ofNat ∘ Node.right)) snapshot.right
      · simpa [insert, sameKind, Grammar.token, operandCount, rootIndices, Expr.nodeCount, written] using roots
    | boolean value =>
      simp [Grammar.pushTree, decoded] at step
      subst after
      have roots := replaceRoots arena.roots (rootIndices before) [] (by simpa using snapshot.roots)
        i (by simpa only [rootLength] using (show before.length < 32 by omega)) (by omega)
      refine ⟨?_, by simp [forestNodes, written, Expr.nodeCount]⟩
      constructor
      · simpa [insert, sameKind, Grammar.token, forestNodes, Expr.nodesFrom, written] using
          appendCell arena.kinds ((forestNodes before).map Node.kind) 2 snapshot.kinds
      · simpa [insert, sameValue, Grammar.token, forestNodes, Expr.nodesFrom, written] using
          appendCell arena.values ((forestNodes before).map Node.value) (Value.boolean value).encode snapshot.values
      · simpa [insert, sameStart, forestNodes, Expr.nodesFrom, written] using
          appendCell arena.offsets ((forestNodes before).map (UInt16.ofNat ∘ Node.start))
            (UInt16.ofNat tok.start) snapshot.offsets
      · simpa [insert, sameKind, Grammar.token, operandCount, forestNodes, Expr.nodesFrom] using
          appendZero arena.left ((forestNodes before).map (UInt8.ofNat ∘ Node.left)) snapshot.left
      · simpa [insert, sameKind, Grammar.token, operandCount, forestNodes, Expr.nodesFrom] using
          appendZero arena.right ((forestNodes before).map (UInt8.ofNat ∘ Node.right)) snapshot.right
      · simpa [insert, sameKind, Grammar.token, operandCount, rootIndices, Expr.nodeCount, written] using roots
    | unary =>
      cases before with
      | nil => simp [Grammar.pushTree, decoded] at step
      | cons child rest =>
        simp [Grammar.pushTree, decoded] at step
        subst after
        let base := forestNodes rest
        let node : Node := ⟨8, 0, tok.start, base.length + child.nodeCount - 1, 0⟩
        have bound : rest.length < 32 := by simp at previous; omega
        have parent : (forestNodes (.unary tok.start child :: rest)) =
            forestNodes (child :: rest) ++ [node] := by
          simp [forestNodes, Expr.nodesFrom, node, base]
        have roots := replaceRoots arena.roots (rootIndices rest)
          [base.length + child.nodeCount - 1] (by simpa [rootIndices, base] using snapshot.roots)
          i (by simpa only [rootLength] using bound) (by omega)
        have prevRoot := rootByte arena child rest snapshot
        have last : base.length + (Expr.unary tok.start child).nodeCount - 1 = i := by
          simp [forestNodes, Expr.nodeCount, base] at written ⊢
          omega
        refine ⟨?_, by simp [parent, written]⟩
        constructor
        · simpa [insert, sameKind, Grammar.token, parent, node, written] using
            appendCell arena.kinds ((forestNodes (child :: rest)).map Node.kind) 8 snapshot.kinds
        · simpa [insert, sameValue, Grammar.token, parent, node, written] using
            appendCell arena.values ((forestNodes (child :: rest)).map Node.value) 0 snapshot.values
        · simpa [insert, sameStart, parent, node, written] using
            appendCell arena.offsets ((forestNodes (child :: rest)).map (UInt16.ofNat ∘ Node.start))
              (UInt16.ofNat tok.start) snapshot.offsets
        · simpa [insert, sameKind, Grammar.token, operandCount, parent, node, written, prevRoot, base] using
            appendCell arena.left ((forestNodes (child :: rest)).map (UInt8.ofNat ∘ Node.left))
              (UInt8.ofNat node.left) snapshot.left
        · simpa [insert, sameKind, Grammar.token, operandCount, parent, node] using
            appendZero arena.right ((forestNodes (child :: rest)).map (UInt8.ofNat ∘ Node.right)) snapshot.right
        · simpa [insert, sameKind, Grammar.token, operandCount, rootIndices, base, last] using roots
    | binary op =>
      cases before with
      | nil => simp [Grammar.pushTree, decoded] at step
      | cons lhs tail =>
        cases tail with
        | nil => simp [Grammar.pushTree, decoded] at step
        | cons rhs rest =>
          simp [Grammar.pushTree, decoded] at step
          subst after
          let base := forestNodes rest
          let leftIndex := base.length + rhs.nodeCount + lhs.nodeCount - 1
          let rightIndex := base.length + rhs.nodeCount - 1
          let node : Node := ⟨op.kind, 0, tok.start, leftIndex, rightIndex⟩
          have bound : rest.length < 32 := by simp at previous; omega
          have parent : (forestNodes (.binary op tok.start lhs rhs :: rest)) =
              forestNodes (lhs :: rhs :: rest) ++ [node] := by
            simp [forestNodes, Expr.nodesFrom, node, base, leftIndex, rightIndex]
          have leftRoot : arena.roots.getD (rest.length + 1) 0 = UInt8.ofNat leftIndex := by
            simpa [forestNodes, leftIndex, base] using rootByte arena lhs (rhs :: rest) snapshot
          have rightRoot : arena.roots.getD rest.length 0 = UInt8.ofNat rightIndex := by
            have h := snapshot.roots rest.length (by simp; omega)
            have atIndex : (arena.roots.getD rest.length 0).toNat = rightIndex := by
              simpa [rootIndices, List.append_assoc, List.getElem_append_right, forestNodes, base,
                leftIndex, rightIndex] using h
            rw [← atIndex, UInt8.ofNat_toNat]
          have roots := replaceRoots arena.roots (rootIndices rest)
            [rightIndex, leftIndex] (by simpa [rootIndices, List.append_assoc, forestNodes, base, rightIndex,
              leftIndex] using snapshot.roots) i (by simpa only [rootLength] using bound) (by omega)
          have last : base.length + (Expr.binary op tok.start lhs rhs).nodeCount - 1 = i := by
            simp [forestNodes, Expr.nodeCount, base] at written ⊢
            omega
          have kindMatches : Grammar.binaryKind op = op.kind := by cases op <;> rfl
          have arityTwo : operandCount op.kind = 2 := by cases op <;> rfl
          refine ⟨?_, by simp [parent, written]⟩
          constructor
          · simpa [insert, sameKind, Grammar.token, parent, node, written, kindMatches] using
              appendCell arena.kinds ((forestNodes (lhs :: rhs :: rest)).map Node.kind) op.kind snapshot.kinds
          · simpa [insert, sameValue, Grammar.token, parent, node, written] using
              appendCell arena.values ((forestNodes (lhs :: rhs :: rest)).map Node.value) 0 snapshot.values
          · simpa [insert, sameStart, parent, node, written] using
              appendCell arena.offsets ((forestNodes (lhs :: rhs :: rest)).map (UInt16.ofNat ∘ Node.start))
                (UInt16.ofNat tok.start) snapshot.offsets
          · simpa [insert, sameKind, Grammar.token, kindMatches, arityTwo, parent, node, written, leftRoot] using
              appendCell arena.left ((forestNodes (lhs :: rhs :: rest)).map (UInt8.ofNat ∘ Node.left))
                (UInt8.ofNat leftIndex) snapshot.left
          · simpa [insert, sameKind, Grammar.token, kindMatches, arityTwo, parent, node, written, rightRoot] using
              appendCell arena.right ((forestNodes (lhs :: rhs :: rest)).map (UInt8.ofNat ∘ Node.right))
                (UInt8.ofNat rightIndex) snapshot.right
          · simpa [insert, sameKind, Grammar.token, kindMatches, arityTwo, rootIndices, base, last] using roots

private def progress (todo : List Token) (forest : List Expr) : Option (List Expr) :=
  match todo with
  | [] => some forest
  | next :: rest => (Grammar.pushTree next forest).bind (progress rest)

private theorem progressAppend (first second : List Token) (forest : List Expr) :
    progress (first ++ second) forest = (progress first forest).bind (progress second) := by
  induction first generalizing forest with
  | nil => rfl
  | cons head tail ih =>
    cases pushed : Grammar.pushTree head forest with
    | none => simp [progress, pushed]
    | some after => simpa [progress, pushed] using ih after

private theorem progressMatches (source : List Token) :
    progress source.reverse [] = Grammar.parseForest source := by
  induction source with
  | nil => rfl
  | cons head tail ih =>
    rw [List.reverse_cons, progressAppend, ih]
    simp [Grammar.parseForest, progress]

private theorem operandShape (tok : Token) (forest : List Expr) (legal : Grammar.form tok ≠ none) :
    (Grammar.pushTree tok forest = none ↔ forest.length < operandCount tok.kind) ∧
      (∀ after, Grammar.pushTree tok forest = some after →
        after.length = forest.length - operandCount tok.kind + 1) := by
  cases found : Grammar.form tok with
  | none => contradiction
  | some f =>
    have canonical := Grammar.token_of_form found
    have tk : tok.kind = (Grammar.token tok.start f).kind := congrArg Token.kind canonical.symm
    cases f with
    | integer value =>
      simp [Grammar.pushTree, found, tk, Grammar.token, operandCount]
    | boolean value =>
      simp [Grammar.pushTree, found, tk, Grammar.token, operandCount]
    | unary =>
      cases forest <;> simp [Grammar.pushTree, found, tk, Grammar.token, operandCount]
    | binary op =>
      have kind : operandCount tok.kind = 2 := by rw [tk]; cases op <;> rfl
      rcases forest with _ | ⟨left, _ | ⟨right, rest⟩⟩ <;>
        simp [Grammar.pushTree, found, kind]

private theorem layoutDone (input : tokens) (arena : Arena) (expr : Expr)
    (count : input.«field:Count».toNat = expr.nodeCount)
    (size : expr.nodeCount ≤ 32) (snapshot : Snapshot arena [expr]) :
    Layout ⟨arena.kinds, arena.values, arena.offsets, arena.left, arena.right, input.«field:Count»⟩ expr := by
  refine ⟨by simpa using count, ?_⟩
  intro i valid
  have within : i < 32 := by simpa using Nat.lt_of_lt_of_le valid (by simpa using size)
  have member : (expr.nodesFrom 0)[i] ∈ expr.nodesFrom 0 := List.getElem_mem valid
  obtain ⟨left, right⟩ := expr.childBounds 0 _ member
  have leftFits : (expr.nodesFrom 0)[i].left < 256 := by omega
  have rightFits : (expr.nodesFrom 0)[i].right < 256 := by omega
  have kinds := snapshot.kinds i within
  have values := snapshot.values i within
  have offsets := snapshot.offsets i within
  have lefts := congrArg UInt8.toNat (snapshot.left i within)
  have rights := congrArg UInt8.toNat (snapshot.right i within)
  have read : (expr.nodesFrom 0)[i]? = some (expr.nodesFrom 0)[i] := List.getElem?_eq_getElem valid
  simp [forestNodes, read] at kinds values offsets
  simp [forestNodes, read, Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits] at lefts rights
  exact ⟨kinds, values, offsets, lefts, rights⟩

private def MatchesForest (input : tokens) (result : tree × Diagnostic) :
    Option (List Expr) → Prop
  | some [expr] => ∃ arena, result = (arena, ⟨0, 0⟩) ∧ Layout arena expr
  | _ => result = syntaxError input

private theorem runs (input : tokens) (todo : List Token) (forest : List Expr) (arena : Arena)
    (i : Nat) (count : input.«field:Count».toNat ≤ 32)
    (remaining : i + todo.length = input.«field:Count».toNat)
    (written : (forestNodes forest).length = i) (snapshot : Snapshot arena forest)
    (aligned : ∀ j (h : j < todo.length), inputToken input (todo.length - 1 - j) = todo[j])
    (canonical : ∀ t ∈ todo, Grammar.form t ≠ none) :
    MatchesForest input (parseRemaining input todo.length i forest.length arena) (progress todo forest) := by
  induction todo generalizing forest arena i with
  | nil =>
    rcases forest with _ | ⟨expr, _ | ⟨next, rest⟩⟩
    · rfl
    · have nodes : expr.nodeCount = i := by simpa [forestNodes] using written
      simp only [List.length_nil, parseRemaining, List.length_cons, Nat.zero_add, ↓reduceIte,
        progress, MatchesForest]
      exact ⟨_, rfl, layoutDone input arena expr (by simp at remaining; omega) (by omega) snapshot⟩
    · simp [progress, MatchesForest, parseRemaining]
  | cons head tail ih =>
    have next : inputToken input tail.length = head := by
      have first := aligned 0 (by simp)
      change inputToken input tail.length = head at first
      exact first
    have kind : input.«field:Kind».getD tail.length 0 = head.kind := congrArg Token.kind next
    have shape := operandShape head forest (canonical head (by simp))
    cases pushed : Grammar.pushTree head forest with
    | none =>
      have underflow : forest.length < operandCount head.kind := shape.1.mp pushed
      simp [progress, pushed, parseRemaining, MatchesForest, kind, underflow]
    | some after =>
      have depth := shape.2 after pushed
      have underflow : ¬ forest.length < operandCount head.kind := by
        intro short
        rw [shape.1.mpr short] at pushed
        contradiction
      have update := grows input i tail.length arena forest after snapshot written (by simp at remaining; omega)
        (by simpa only [next] using pushed)
      have restAligned (j : Nat) (valid : j < tail.length) :
          inputToken input (tail.length - 1 - j) = tail[j] := by
        have here := aligned (j+1) (by simp; omega)
        have arithmetic : (head :: tail).length - 1 - (j+1) = tail.length - 1 - j := by simp; omega
        rw [arithmetic] at here
        exact here
      have result := ih after _ (i+1) (by simp at remaining; omega) update.2 update.1 restAligned
        (fun t member => canonical t (by simp [member]))
      simpa [progress, pushed, parseRemaining, kind, underflow, depth] using result

private theorem readsField [OfNat α 0] (project : Token → α) (words : List Token) (i : Nat)
    (valid : i < words.length) (bound : i < 32) :
    (LexerModel.field project 0 words).getD i 0 = project words[i] := by
  rw [getAt _ bound]
  simp [LexerModel.field, List.getElem?_eq_getElem valid]

private theorem readsToken (sourceLength : Nat) (words : List Token) (i : Nat) (valid : i < words.length)
    (count : words.length ≤ 32) (offset : words[i].start < 65536) :
    inputToken (LexerModel.encode sourceLength words) i = words[i] := by
  have bound : i < 32 := by omega
  simp only [inputToken, LexerModel.encode, readsField Token.kind words i valid bound,
    readsField Token.value words i valid bound,
    readsField (UInt16.ofNat ∘ Token.start) words i valid bound, Function.comp_apply]
  have position : (UInt16.ofNat words[i].start).toNat = words[i].start := by
    exact Nat.mod_eq_of_lt offset
  rw [position]

theorem referenceMatchesGrammar (sourceLength : Nat) (words : List Token)
    (size : sourceLength ≤ 256) (count : words.length ≤ 32)
    (canonical : Grammar.Canonical sourceLength words) :
    match Grammar.parse words with
    | some expr =>
      ∃ arena, reference (LexerModel.encode sourceLength words) = (arena, ⟨0, 0⟩) ∧ Layout arena expr
    | none =>
      reference (LexerModel.encode sourceLength words) = syntaxError (LexerModel.encode sourceLength words) := by
  let input := LexerModel.encode sourceLength words
  have length : input.«field:Count».toNat = words.length := by
    simp [input, LexerModel.encode, Nat.mod_eq_of_lt (show words.length < 256 by omega)]
  have aligned (j : Nat) (valid : j < words.reverse.length) :
      inputToken input (words.reverse.length - 1 - j) = words.reverse[j] := by
    rw [List.getElem_reverse valid]
    have wordIndex : words.length - 1 - j < words.length := by simp at valid; omega
    rw [List.length_reverse]
    exact readsToken sourceLength words _ wordIndex count
      (Nat.lt_of_le_of_lt (canonical _ (List.getElem_mem wordIndex)).2 (by omega))
  have matched := runs input words.reverse [] {} 0 (by omega) (by simp [length]) rfl initial aligned
    (fun t membership => (canonical t (by simpa using membership)).1)
  have normalized : reference input = parseRemaining input words.reverse.length 0 0 {} := by
    simp [reference, length, show ¬ 32 < words.length by omega]
  change MatchesForest input (parseRemaining input words.reverse.length 0 0 {})
    (progress words.reverse []) at matched
  rw [progressMatches, ← normalized] at matched
  change MatchesForest input (reference input) (Grammar.parseForest words) at matched
  unfold Grammar.parse
  cases parsed : Grammar.parseForest words with
  | none => simpa [parsed, MatchesForest] using matched
  | some forest =>
    rcases forest with _ | ⟨expr, _ | ⟨next, rest⟩⟩ <;>
      simpa [parsed, MatchesForest] using matched

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Parser
