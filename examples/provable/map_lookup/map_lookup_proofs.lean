-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import map_lookup.map_lookup_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/map_lookup».map_lookup

-- The draft represents maps as association lists with unique keys and nil as empty.
theorem missingKeyUsesFallback (key fallback : Int64) :
    ReadOr ([] : List (Int64 × Int64)) key fallback = fallback := by
  sorry

theorem presentZeroIsAValue (key : Int64) : ReadOr [(key, 0)] key 9 = 0 := by
  sorry
