import map_build.map_build_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/map_build».map_build

-- A singleton association list specifies the observable map contents.
theorem lastWriteWins (key first last : Int64) :
    Overwrite key first last = some ([(key, last)] : List (Int64 × Int64)) := by
  simp [Overwrite]

theorem distinctKeysRetainBothValues (firstKey lastKey first last : Int64) (different : firstKey ≠ lastKey) :
    (WriteTwoKeys firstKey lastKey first last).bind (List.lookup firstKey) = some first ∧
    (WriteTwoKeys firstKey lastKey first last).bind (List.lookup lastKey) = some last := by
  have firstDiffers : (firstKey == lastKey) = false := beq_eq_false_iff_ne.mpr different
  have lastDiffers : (lastKey == firstKey) = false := beq_eq_false_iff_ne.mpr (Ne.symm different)
  simp [WriteTwoKeys, List.lookup, firstDiffers, lastDiffers]
