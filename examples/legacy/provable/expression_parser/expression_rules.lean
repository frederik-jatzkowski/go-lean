namespace ExpressionRules

abbrev Bytes := Option (List UInt8 × Nat)

def contents (xs : Bytes) : List UInt8 := (xs.getD ([], 0)).1

def digit (b : UInt8) : Bool := decide (48 ≤ b ∧ b ≤ 57)

def lex (inRun : Bool) : List UInt8 → List UInt8 × Bool
  | [] => ([], true)
  | b :: tail =>
    if digit b then
      let rest := lex true tail
      (if inRun then rest.1 else 1 :: rest.1, rest.2)
    else if b = 43 then
      let rest := lex false tail
      (2 :: rest.1, rest.2)
    else if b = 45 then
      let rest := lex false tail
      (3 :: rest.1, rest.2)
    else ([], false)

-- The two phases are the productions for needing a number and having read one.
def tokenGrammar (needNumber : Bool) : List UInt8 → Bool
  | [] => !needNumber
  | token :: tail =>
    if needNumber then decide (token = 1) && tokenGrammar false tail
    else decide (token = 2 ∨ token = 3) && tokenGrammar true tail

-- At the byte level an existing number can also continue with another digit.
def byteGrammar (needDigit : Bool) : List UInt8 → Bool
  | [] => !needDigit
  | b :: tail =>
    if needDigit then digit b && byteGrammar false tail
    else if digit b then byteGrammar false tail
    else decide (b = 43 ∨ b = 45) && byteGrammar true tail

end ExpressionRules
