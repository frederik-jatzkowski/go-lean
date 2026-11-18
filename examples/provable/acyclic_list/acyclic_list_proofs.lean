-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import acyclic_list.acyclic_list_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/acyclic_list».acyclic_list

-- A list models finite acyclic chains. Recursion decreases the remaining list length.
theorem lengthMatchesStructuralLength (xs : List Int64) :
    Length xs = Int64.ofNat xs.length := by
  sorry
