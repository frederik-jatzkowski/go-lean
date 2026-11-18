import generic_map.generic_map_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/generic_map».generic_map

theorem incrementAllIsMap (xs : List Int64) :
    IncrementAll xs = some (xs.map (fun x => x + 1)) := by
  rfl
