-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import map_build.map_build_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/map_build».map_build

-- A singleton association list specifies the observable map contents.
theorem lastWriteWins (key first last : Int64) :
    Overwrite key first last = some ([(key, last)] : List (Int64 × Int64)) := by
  sorry
