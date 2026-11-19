package batchfulfillment

import (
	"slices"
	"testing"
)

func TestRejectedOrderStaysAtTheCursor(t *testing.T) {
	pending := []Order{{7}, {2}, {3}, {1}}
	batch := Batch{stock: 4, orders: slices.Clone(pending), cursor: 1}
	if !batch.Fulfill() || batch.stock != 2 || batch.cursor != 2 || !slices.Equal(batch.orders, pending) {
		t.Fatalf("first fulfillment: %+v", batch)
	}
	batch.stock++
	if !batch.Fulfill() || batch.stock != 0 || batch.cursor != 3 || !slices.Equal(batch.orders, pending) {
		t.Fatalf("resumed fulfillment: %+v", batch)
	}
}
