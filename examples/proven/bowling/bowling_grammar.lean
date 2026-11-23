namespace Bowling.Grammar

inductive Token where
  | count (pins : Int64)
  | comma
  deriving DecidableEq

/-- Single-byte spellings. Whitespace contributes no token. -/
def single (b : UInt8) : Option (List Token) :=
  if b = 44 then some [.comma]
  else if b = 32 ∨ b = 9 ∨ b = 13 ∨ b = 10 then some []
  else if 48 ≤ b ∧ b ≤ 57 then some [.count (Int64.ofNat (b.toNat - 48))]
  else none

/-- The only two-byte spelling is 10. Return the tokens rightmost first. -/
def spell : List UInt8 → Option (List Token)
  | [] => some []
  | b :: rest =>
    if b = 49 then
      match rest with
      | c :: tail =>
        if c = 48 then (spell tail).map (· ++ [.count 10])
        else (spell (c :: tail)).map (· ++ [.count 1])
      | [] => some [.count 1]
    else (single b).bind fun ts => (spell rest).map (· ++ ts)

/-- Read a nonempty comma-separated list from right to left. -/
def nonempty : List Token → Option (List Int64)
  | [.count n] => some [n]
  | .count n :: .comma :: rest => (nonempty rest).map (· ++ [n])
  | _ => none

def counts (tokens : List Token) : Option (List Int64) :=
  if tokens.isEmpty then some [] else nonempty tokens

def Parses (bytes : List UInt8) (attempts : List Int64) : Prop :=
  ((spell bytes).bind counts) = some attempts

end Bowling.Grammar
