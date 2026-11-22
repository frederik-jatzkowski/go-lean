import acyclic_list.acyclic_list_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/acyclic_list».acyclic_list.Proofs

-- A list models finite acyclic chains. Recursion decreases the remaining list length.
theorem lengthMatchesStructuralLength : Laws.lengthMatchesStructuralLength := by
  intro xs
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    change 1 + Length tail = Int64.ofNat (tail.length + 1)
    rw [ih, Int64.ofNat_add]
    exact Int64.add_comm _ _

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/acyclic_list».acyclic_list.Proofs
