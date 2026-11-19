import subset.check_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/internal/subset».check

-- TestBinaryOperatorEncodings checks these numbers against Go's named constants.
theorem binarySupportedTokens :
    Binary 12 = (0, true) ∧ Binary 13 = (1, true) ∧ Binary 14 = (2, true) ∧
    Binary 15 = (3, true) ∧ Binary 16 = (4, true) ∧ Binary 39 = (5, true) ∧
    Binary 44 = (6, true) ∧ Binary 40 = (7, true) ∧ Binary 45 = (8, true) ∧
    Binary 41 = (9, true) ∧ Binary 46 = (10, true) := by
  decide

theorem binaryRejectsOtherTokens (op : GoTypes.Int)
    (h12 : op ≠ 12) (h13 : op ≠ 13) (h14 : op ≠ 14)
    (h15 : op ≠ 15) (h16 : op ≠ 16) (h39 : op ≠ 39)
    (h44 : op ≠ 44) (h40 : op ≠ 40) (h45 : op ≠ 45)
    (h41 : op ≠ 41) (h46 : op ≠ 46) :
    Binary op = (0, false) := by
  simp [Binary, h12, h13, h14, h15, h16, h39, h44, h40, h45, h41, h46]
