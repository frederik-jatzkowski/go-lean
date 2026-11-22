import assumed_reflection.assumed_reflection_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/assumed_reflection».assumed_reflection.Proofs

theorem agreesWithSign : Laws.agreesWithSign := by
  intro reader
  dsimp only
  intro r
  change decide ((0 : Int64) ≤ reader.operation r) = decide (0 ≤ r)
  have reading : reader.operation r = r := reader.returnsReading r
  rw [reading]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/assumed_reflection».assumed_reflection.Proofs
