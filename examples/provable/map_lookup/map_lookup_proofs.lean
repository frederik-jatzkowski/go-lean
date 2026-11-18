import map_lookup.map_lookup_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/map_lookup».map_lookup

-- Valid map representations have unique keys. Nil maps use the empty list.
theorem missingKeyUsesFallback (key fallback : Int64) :
    ReadOr ([] : List (Int64 × Int64)) key fallback = fallback := by
  rfl

theorem presentZeroIsAValue (key : Int64) : ReadOr [(key, 0)] key 9 = 0 := by
  simp [ReadOr]

theorem missingKeyInNonemptyMap (entry key value fallback : Int64) (different : key ≠ entry) :
    ReadOr [(entry, value)] key fallback = fallback := by
  have keyMiss : (key == entry) = false := beq_eq_false_iff_ne.mpr different
  simp [ReadOr, List.lookup, keyMiss]
