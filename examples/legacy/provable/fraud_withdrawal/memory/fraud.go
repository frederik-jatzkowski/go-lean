// Package memory provides an in-memory implementation of the fraud policy.
package memory

// Fraud blocks withdrawals at or above BlockAt and always blocks account zero.
type Fraud struct {
	BlockAt uint64
}

func (policy Fraud) Blocked(accountID, amount uint64) bool {
	return accountID == 0 || amount >= policy.BlockAt
}
