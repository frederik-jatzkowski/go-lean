package batchfulfillment

type Order struct {
	Quantity int64
}

type Batch struct {
	stock  int64
	orders []Order
	cursor int
}

// Fulfill processes pending orders until one is invalid or exceeds stock.
// It reports whether the current order was rejected.
//
//golean:verify
func (batch *Batch) Fulfill() bool {
	for batch.cursor < len(batch.orders) {
		order := batch.orders[batch.cursor]
		if order.Quantity <= 0 || order.Quantity > batch.stock {
			return true
		}
		batch.stock -= order.Quantity
		batch.cursor++
	}
	return false
}
