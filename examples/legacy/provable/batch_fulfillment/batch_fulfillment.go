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
//golean:verify nonnegativeAndConservesStock : ∀ (batch final : Batch) (rejected : Bool) (nonnegative : 0 ≤ batch.«field:stock»)
//golean:verify+   (result : «Batch$Fulfill» (some batch) = some (some final, rejected)),
//golean:verify+   final.«field:orders» = batch.«field:orders» ∧ 0 ≤ final.«field:stock» ∧
//golean:verify+     ∃ shipped : List Int,
//golean:verify+       shipped.foldr (fun quantity tail cursor =>
//golean:verify+         ∃ order : Order, (batch.«field:orders».getD [])[cursor.toNatClampNeg]? = some order ∧
//golean:verify+           0 < order.«field:Quantity» ∧ quantity = order.«field:Quantity».toInt ∧ tail (cursor + 1))
//golean:verify+         (fun cursor => cursor = final.«field:cursor») batch.«field:cursor» ∧
//golean:verify+       batch.«field:stock».toInt = final.«field:stock».toInt + shipped.sum
//golean:verify rejectedOrderStaysAtTheCursor : let pending : Option (List Order) := some [⟨7⟩, ⟨2⟩, ⟨3⟩, ⟨1⟩]
//golean:verify+ «Batch$Fulfill» (some ⟨4, pending, 1⟩) = some (some ⟨2, pending, 2⟩, true)
//golean:verify resumedBatchProcessesPreviouslyRejectedOrder : let pending : Option (List Order) := some [⟨7⟩, ⟨2⟩, ⟨3⟩, ⟨1⟩]
//golean:verify+ «Batch$Fulfill» (some ⟨3, pending, 2⟩) = some (some ⟨0, pending, 3⟩, true)
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
