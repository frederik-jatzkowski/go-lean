import map_lookup.map_lookup_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/map_lookup».map_lookup.Proofs

-- Valid map representations have unique keys. Nil maps use the empty list.
theorem missingKeyUsesFallback : Laws.missingKeyUsesFallback := by
  intro key fallback
  rfl

theorem presentZeroIsAValue : Laws.presentZeroIsAValue := by
  intro key
  simp [ReadOr]

theorem missingKeyInNonemptyMap : Laws.missingKeyInNonemptyMap := by
  intro entry key value fallback different
  have keyMiss : (key == entry) = false := beq_eq_false_iff_ne.mpr different
  simp [ReadOr, List.lookup, keyMiss]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/map_lookup».map_lookup.Proofs
