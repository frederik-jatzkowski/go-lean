package fraudwithdrawal

// FraudRepository supplies the fraud decision for a proposed withdrawal.
type FraudRepository interface {
	//golean:assume unknownAccountBlocked : ∀ repo amount, Blocked repo 0 amount = true
	Blocked(accountID, amount uint64) bool
}

// BalanceRepository stores account balances. Absent accounts have balance zero.
type BalanceRepository interface {
	Balance(accountID uint64) uint64
	//golean:assume returnsStoredBalance : ∀ repo accountID balance, SetBalance repo accountID balance = balance
	SetBalance(accountID, balance uint64) uint64
}

type WithdrawalService struct {
	//golean:assume:initialized
	fraud FraudRepository
	//golean:assume:initialized
	balances BalanceRepository
}

// NewWithdrawalService requires initialized fraud and balance repositories.
//
//golean:verify:constructor
func NewWithdrawalService(fraud FraudRepository, balances BalanceRepository) WithdrawalService {
	return WithdrawalService{fraud: fraud, balances: balances}
}

func (service WithdrawalService) blocked(accountID, amount uint64) bool {
	return service.fraud.Blocked(accountID, amount)
}

// Withdraw saves an approved debit and returns the balance reported by the repository.
//
//golean:boundary BalanceRepository.Balance readonly
//golean:boundary FraudRepository.Blocked readonly
//golean:boundary BalanceRepository.SetBalance effect
//golean:verify blockedPreservesBalance : ∀ {B F : Type} (balances : InterfaceContracts.BalanceRepositoryContract B)
//golean:verify+   (fraud : InterfaceContracts.FraudRepositoryContract F) (service : WithdrawalService B F)
//golean:verify+   (accountID amount : UInt64),
//golean:verify+   fraud.Blocked service.«field:fraud» accountID amount = true →
//golean:verify+   «WithdrawalService$Withdraw» balances fraud service accountID amount =
//golean:verify+     ((balances.Balance service.«field:balances» accountID, false), [])
//golean:verify invalidAmountPreservesBalance : ∀ {B F : Type} (balances : InterfaceContracts.BalanceRepositoryContract B)
//golean:verify+   (fraud : InterfaceContracts.FraudRepositoryContract F) (service : WithdrawalService B F)
//golean:verify+   (accountID amount : UInt64),
//golean:verify+   amount = 0 ∨ balances.Balance service.«field:balances» accountID < amount →
//golean:verify+   «WithdrawalService$Withdraw» balances fraud service accountID amount =
//golean:verify+     ((balances.Balance service.«field:balances» accountID, false), [])
//golean:verify rejectedWithdrawHasNoEffect : ∀ {B F : Type} (balances : InterfaceContracts.BalanceRepositoryContract B)
//golean:verify+   (fraud : InterfaceContracts.FraudRepositoryContract F) (service : WithdrawalService B F)
//golean:verify+   (accountID amount : UInt64),
//golean:verify+   let result := «WithdrawalService$Withdraw» balances fraud service accountID amount
//golean:verify+   result.1.2 = false →
//golean:verify+     result.1.1 = balances.Balance service.«field:balances» accountID ∧ result.2 = []
//golean:verify approvedWithdrawWritesOnce : ∀ {B F : Type} (balances : InterfaceContracts.BalanceRepositoryContract B)
//golean:verify+   (fraud : InterfaceContracts.FraudRepositoryContract F) (service : WithdrawalService B F)
//golean:verify+   (accountID amount : UInt64),
//golean:verify+   fraud.Blocked service.«field:fraud» accountID amount = false →
//golean:verify+   amount ≠ 0 → ¬ balances.Balance service.«field:balances» accountID < amount →
//golean:verify+   «WithdrawalService$Withdraw» balances fraud service accountID amount =
//golean:verify+     ((balances.Balance service.«field:balances» accountID - amount, true),
//golean:verify+       ["github.com/frederik-jatzkowski/go-lean/examples/provable/fraud_withdrawal.BalanceRepository.SetBalance"])
func (service WithdrawalService) Withdraw(accountID, amount uint64) (balance uint64, withdrawn bool) {
	balance, approved := service.planWithdrawal(accountID, amount)
	if !approved {
		return balance, false
	}
	return service.balances.SetBalance(accountID, balance), true
}

// planWithdrawal reads the current balance and computes the debit decision.
func (service WithdrawalService) planWithdrawal(accountID, amount uint64) (balance uint64, approved bool) {
	balance = service.balances.Balance(accountID)
	if service.blocked(accountID, amount) {
		return balance, false
	}
	if amount == 0 || balance < amount {
		return balance, false
	}
	return balance - amount, true
}
