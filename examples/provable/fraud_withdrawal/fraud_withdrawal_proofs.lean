import fraud_withdrawal.fraud_withdrawal_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/fraud_withdrawal».fraud_withdrawal.Proofs

theorem blockedPreservesBalance : Laws.blockedPreservesBalance := by
  intro B F balances fraud service accountID amount blocked
  simp [«WithdrawalService$Withdraw», «WithdrawalService$planWithdrawal»,
    «WithdrawalService$blocked», blocked]

theorem invalidAmountPreservesBalance : Laws.invalidAmountPreservesBalance := by
  intro B F balances fraud service accountID amount invalid
  rcases invalid with zero | overdraft
  · simp [«WithdrawalService$Withdraw», «WithdrawalService$planWithdrawal», zero]
  · simp [«WithdrawalService$Withdraw», «WithdrawalService$planWithdrawal», overdraft]

theorem approvedWithdrawWritesOnce : Laws.approvedWithdrawWritesOnce := by
  intro B F balances fraud service accountID amount clear positive enough
  simp [«WithdrawalService$Withdraw», «WithdrawalService$planWithdrawal»,
    «WithdrawalService$blocked», clear, positive, enough, balances.returnsStoredBalance]

theorem rejectedWithdrawHasNoEffect : Laws.rejectedWithdrawHasNoEffect := by
  intro B F balances fraud service accountID amount
  dsimp only
  cases blocked : fraud.Blocked service.«field:fraud» accountID amount with
  | true =>
    rw [blockedPreservesBalance balances fraud service accountID amount blocked]
    simp
  | false =>
    by_cases invalid : amount = 0 ∨ balances.Balance service.«field:balances» accountID < amount
    · rw [invalidAmountPreservesBalance balances fraud service accountID amount invalid]
      simp
    · have positive : amount ≠ 0 := fun zero => invalid (Or.inl zero)
      have enough : ¬ balances.Balance service.«field:balances» accountID < amount :=
        fun overdraft => invalid (Or.inr overdraft)
      rw [approvedWithdrawWritesOnce balances fraud service accountID amount blocked positive enough]
      simp

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/fraud_withdrawal».fraud_withdrawal.Proofs
