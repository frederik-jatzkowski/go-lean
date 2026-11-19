package main

import (
	"fmt"
	"log"
	"time"

	orders "github.com/frederik-jatzkowski/go-lean/examples/provable/order_service"
)

type memoryRepository map[uint64]orders.Order

func (repo memoryRepository) Get(id uint64) orders.Order { return repo[id] }

func (repo memoryRepository) Persist(order orders.Order) { repo[order.ID()] = order }

func main() {
	const id, sku = 7, 1
	offer := orders.Search(sku)
	fmt.Printf("SKU %d available: %t, price: %d cents\n", sku, offer.Available, offer.PriceCents)

	service := orders.NewService(make(memoryRepository))
	start := time.Date(2026, time.November, 19, 12, 0, 0, 0, time.UTC)
	deadline := start.Add(24 * time.Hour)
	now, due := orders.Timestamp(start.UnixMicro()), orders.Timestamp(deadline.UnixMicro())
	if _, problem := service.Place(id, sku, now, due); problem != orders.OK {
		log.Fatalf("placement failed: %v", problem)
	}
	bill, problem := service.GetBill(id)
	if problem != orders.OK {
		log.Fatalf("bill lookup failed: %v", problem)
	}
	billDue := time.UnixMicro(int64(bill.DueAt)).UTC()
	fmt.Printf("Bill for order %d: %d cents, due %s\n", bill.OrderID, bill.PriceCents, billDue.Format(time.RFC3339))

	if _, problem := service.Cancel(id, due-1); problem != orders.OK {
		log.Fatalf("cancellation failed: %v", problem)
	}
	bill, problem = service.GetBill(id)
	if problem != orders.OK {
		log.Fatalf("bill lookup failed: %v", problem)
	}
	fmt.Printf("Order %d cancelled, bill void: %t\n", id, bill.Void)
}
