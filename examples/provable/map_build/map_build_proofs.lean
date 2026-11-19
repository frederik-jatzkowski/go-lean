import map_build.map_build_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/map_build».map_build.Proofs

-- A singleton association list specifies the observable map contents.
theorem lastWriteWins : Laws.lastWriteWins := by
  intro key first last
  simp [Overwrite]

theorem distinctKeysRetainBothValues : Laws.distinctKeysRetainBothValues := by
  intro firstKey lastKey first last different
  have firstDiffers : (firstKey == lastKey) = false := beq_eq_false_iff_ne.mpr different
  have lastDiffers : (lastKey == firstKey) = false := beq_eq_false_iff_ne.mpr (Ne.symm different)
  simp [WriteTwoKeys, List.lookup, firstDiffers, lastDiffers]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/map_build».map_build.Proofs
