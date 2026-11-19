import fraud_withdrawal.fraud_withdrawal_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/fraud_withdrawal».fraud_withdrawal.Proofs

theorem blockedPreservesBalance : Laws.blockedPreservesBalance := by
  intro B F balances fraud service accountID amount blocked
  simp [«WithdrawalService$planWithdrawal», «WithdrawalService$blocked», blocked]

theorem invalidAmountPreservesBalance : Laws.invalidAmountPreservesBalance := by
  intro B F balances fraud service accountID amount invalid
  rcases invalid with zero | overdraft
  · simp [«WithdrawalService$planWithdrawal», zero]
  · simp [«WithdrawalService$planWithdrawal», overdraft]

theorem approvedDeductsAmount : Laws.approvedDeductsAmount := by
  intro B F balances fraud service accountID amount clear positive withinBalance
  simp [«WithdrawalService$planWithdrawal», «WithdrawalService$blocked», clear, positive, withinBalance]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/fraud_withdrawal».fraud_withdrawal.Proofs
