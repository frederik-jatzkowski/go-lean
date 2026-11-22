import expression_parser.expression_parser_laws

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/expression_parser».expression_parser.Proofs

open ExpressionRules

private theorem replaceFold (f g : σ → α → σ) (initial : σ) (xs : List α)
    (same : ∀ state value, f state value = g state value) :
    xs.foldl f initial = xs.foldl g initial := by
  rw [show f = g from funext fun state => funext (same state)]

private abbrev LexState := Bytes × Bool × Bool

private def push (out : Bytes) (kind : UInt8) : Bytes :=
  out.map fun (tokens, capacity) => (tokens ++ [kind], capacity)

private def lexStep (state : LexState) (b : UInt8) : LexState :=
  let (out, valid, inRun) := state
  if !valid then state
  else if digit b then (if inRun then out else push out 1, true, true)
  else if b = 43 then (push out 2, true, false)
  else if b = 45 then (push out 3, true, false)
  else (out, false, inRun)

private theorem lexStopped (xs : List UInt8) (out : Bytes) (inRun : Bool) :
    xs.foldl lexStep (out, false, inRun) = (out, false, inRun) := by
  induction xs with
  | nil => rfl
  | cons b tail ih => simpa [lexStep] using ih

private theorem lexFold (xs acc : List UInt8) (capacity : Nat) (inRun : Bool) :
    let result := xs.foldl lexStep (some (acc, capacity), true, inRun)
    let expected := lex inRun xs
    (result.1, result.2.1) = (some (acc ++ expected.1, capacity), expected.2) := by
  induction xs generalizing acc inRun with
  | nil => simp [lex]
  | cons b tail ih =>
    by_cases d : digit b = true
    · cases inRun <;> simp_all [lex, lexStep, push, List.append_assoc]
    by_cases plus : b = 43
    · simp_all [lex, lexStep, push, List.append_assoc]
    by_cases minus : b = 45
    · simp_all [lex, lexStep, push, List.append_assoc]
    simp_all [lex, lexStep, lexStopped]

theorem tokenizes : Laws.tokenizes := by
  intro input
  unfold Tokenize
  rw [replaceFold (g := lexStep)]
  · exact lexFold (contents input) [] (contents input).length false
  · rintro ⟨out, valid, inRun⟩ b
    change _ = lexStep (out, valid, inRun) b
    by_cases lo : (48 : UInt8) ≤ b <;> by_cases hi : b ≤ (57 : UInt8) <;>
      by_cases plus : b = 43 <;> by_cases minus : b = 45 <;>
      cases valid <;> cases inRun <;> simp_all [lexStep, digit, push] <;> split <;> simp_all

private def parseStep (state token : UInt8) : UInt8 :=
  if state = 0 ∧ token = 1 then 1
  else if state = 1 ∧ (token = 2 ∨ token = 3) then 0
  else 2

private theorem parseStopped (xs : List UInt8) :
    xs.foldl parseStep 2 = 2 := by
  induction xs with
  | nil => rfl
  | cons token tail ih => simpa [parseStep] using ih

private theorem parseFold (xs : List UInt8) (need : Bool) :
    (decide (xs.foldl parseStep (if need then 0 else 1) = 1)) = tokenGrammar need xs := by
  induction xs generalizing need with
  | nil => cases need <;> decide
  | cons token tail ih =>
    cases need <;> by_cases number : token = 1 <;> by_cases op : token = 2 ∨ token = 3 <;>
      simp_all [parseStep, tokenGrammar, parseStopped]

theorem parses : Laws.parses := by
  intro tokens
  unfold Parse
  rw [replaceFold (g := parseStep)]
  · exact parseFold (contents tokens) true
  · intro state token
    by_cases zero : state = 0 <;> by_cases one : state = 1 <;> by_cases two : state = 2 <;>
      by_cases number : token = 1 <;> by_cases plus : token = 2 <;> by_cases minus : token = 3 <;>
      simp_all [parseStep]

private theorem lexMatches (xs : List UInt8) (inRun : Bool) :
    let t := lex inRun xs
    (t.2 && tokenGrammar (!inRun) t.1) = byteGrammar (!inRun) xs := by
  induction xs generalizing inRun with
  | nil => cases inRun <;> rfl
  | cons b tail ih =>
    by_cases d : digit b = true
    · cases inRun <;> simp_all [lex, tokenGrammar, byteGrammar]
    by_cases plus : b = 43
    · cases inRun <;> simp_all [lex, tokenGrammar, byteGrammar]
    by_cases minus : b = 45
    · cases inRun <;> simp_all [lex, tokenGrammar, byteGrammar]
    cases inRun <;> simp_all [lex, tokenGrammar, byteGrammar]

theorem recognizes : Laws.recognizes := by
  intro input
  unfold Recognize
  rw [tokenizes input]
  have parseLaw (tokens : Bytes) : Parse tokens = tokenGrammar true (contents tokens) := parses tokens
  simp only [parseLaw]
  have equivalence := lexMatches (contents input) false
  change ((lex false (contents input)).2 && tokenGrammar true (lex false (contents input)).1) =
    byteGrammar true (contents input) at equivalence
  cases verdict : (lex false (contents input)).2 <;>
    simp_all [contents]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/expression_parser».expression_parser.Proofs
