package orderservice

import "testing"

type recordingRepository struct {
	orders map[uint64]Order
	writes []Order
}

func (repo *recordingRepository) Get(id uint64) Order {
	return repo.orders[id]
}

func (repo *recordingRepository) Persist(order Order) {
	repo.orders[order.ID()] = order
	repo.writes = append(repo.writes, order)
}

func TestOrderLifecycle(t *testing.T) {
	repo := &recordingRepository{orders: make(map[uint64]Order)}
	service := NewService(repo)
	if got := Search(1); got != (Offer{Available: true, PriceCents: 1250}) {
		t.Fatalf("available offer = %+v", got)
	}
	if got := Search(2); got.Available || got.PriceCents != 2400 {
		t.Fatalf("unavailable offer = %+v", got)
	}
	if got := Search(99); got != (Offer{}) {
		t.Fatalf("unknown offer = %+v", got)
	}
	if bill, problem := service.GetBill(7); bill != (Bill{}) || problem != MissingOrder {
		t.Fatalf("missing bill = %+v, error %v", bill, problem)
	}

	expectRejected := func(got Order, problem OrderError, old Order, want OrderError, writes int) {
		t.Helper()
		if got != old || problem != want || len(repo.writes) != writes {
			t.Fatalf("rejection returned %+v, error %v, writes %d; want %+v, error %v, writes %d",
				got, problem, len(repo.writes), old, want, writes)
		}
	}
	for _, tc := range []struct {
		id, sku  uint64
		now, due Timestamp
		want     OrderError
	}{
		{0, 1, 100, 200, InvalidID},
		{7, 2, 100, 200, Unavailable},
		{7, 99, 100, 200, Unavailable},
		{7, 1, 100, 100, InvalidDue},
		{7, 1, 100, 99, InvalidDue},
	} {
		got, problem := service.Place(tc.id, tc.sku, tc.now, tc.due)
		expectRejected(got, problem, Order{}, tc.want, 0)
	}
	got, problem := service.Cancel(7, 150)
	expectRejected(got, problem, Order{}, MissingOrder, 0)

	placed, problem := service.Place(7, 1, 100, 200)
	wantBill := Bill{OrderID: 7, PriceCents: 1250, DueAt: 200}
	wantPlaced := Order{id: 7, sku: 1, placedAt: 100, bill: wantBill}
	if placed != wantPlaced || problem != OK || len(repo.writes) != 1 || repo.writes[0] != wantPlaced {
		t.Fatalf("placement = %+v, error %v, writes %+v", placed, problem, repo.writes)
	}
	if bill, problem := service.GetBill(7); bill != wantBill || problem != OK || len(repo.writes) != 1 {
		t.Fatalf("issued bill = %+v, error %v, writes %+v", bill, problem, repo.writes)
	}
	got, problem = service.Place(7, 1, 100, 200)
	expectRejected(got, problem, placed, AlreadyPlaced, 1)
	for _, now := range []Timestamp{99, 200, 201} {
		got, problem = service.Cancel(7, now)
		expectRejected(got, problem, placed, OutsideCancellationWindow, 1)
	}

	cancelled, problem := service.Cancel(7, 199)
	wantBill.Void = true
	wantCancelled := wantPlaced
	wantCancelled.bill = wantBill
	if cancelled != wantCancelled || problem != OK || len(repo.writes) != 2 || repo.writes[1] != wantCancelled {
		t.Fatalf("cancellation = %+v, error %v, writes %+v", cancelled, problem, repo.writes)
	}
	if bill, problem := service.GetBill(7); bill != wantBill || problem != OK || len(repo.writes) != 2 {
		t.Fatalf("void bill = %+v, error %v, writes %+v", bill, problem, repo.writes)
	}
	got, problem = service.Cancel(7, 199)
	expectRejected(got, problem, cancelled, AlreadyCancelled, 2)
	got, problem = service.Place(7, 1, 100, 200)
	expectRejected(got, problem, cancelled, AlreadyPlaced, 2)
	if repo.Get(7) != wantCancelled {
		t.Fatal("rejection changed stored order")
	}
}
