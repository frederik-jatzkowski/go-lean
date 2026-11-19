package memory

// Balances stores account balances for sequential use.
type Balances map[uint64]uint64

func (balances Balances) Balance(accountID uint64) uint64 {
	return balances[accountID]
}

func (balances Balances) SetBalance(accountID, balance uint64) uint64 {
	balances[accountID] = balance
	return balance
}
