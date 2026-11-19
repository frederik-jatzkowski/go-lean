// Package orderservice demonstrates verified order transitions and persistence decisions.
//
//golean:verify:import order_service.orders_rules
//golean:verify searchMatchesRules : ∀ sku, Search sku = Rules.search sku
//golean:verify placeMatchesRules : ∀ order id sku now due, «Order$Place» order id sku now due = Rules.place order id sku now due
//golean:verify cancelMatchesRules : ∀ order now, «Order$Cancel» order now = Rules.cancel order now
//golean:verify billMatchesRules : ∀ order, «Order$Bill» order = Rules.bill order
//golean:verify rejectionPreservesOrder : ∀ order command, (Rules.applyGo order command).2 ≠ 0 → (Rules.applyGo order command).1 = order
//golean:verify historiesMatchRules : ∀ commands, Rules.run Rules.applyGo Rules.emptyOrder commands = Rules.run Rules.applySpec Rules.emptyOrder commands
//golean:verify historiesPreserveValidity : ∀ commands, Rules.Valid (Rules.run Rules.applyGo Rules.emptyOrder commands).1
package orderservice

// Timestamp is a wall-clock Unix timestamp in microseconds.
type Timestamp int64

// OrderError is a domain rejection code. Compare the concrete result with OK.
type OrderError uint8

const (
	OK OrderError = iota
	InvalidID
	AlreadyPlaced
	Unavailable
	InvalidDue
	MissingOrder
	AlreadyCancelled
	OutsideCancellationWindow
)

func (problem OrderError) Error() string {
	switch problem {
	case OK:
		return "success"
	case InvalidID:
		return "invalid order ID"
	case AlreadyPlaced:
		return "order already placed"
	case Unavailable:
		return "good unavailable"
	case InvalidDue:
		return "bill must be due after placement"
	case MissingOrder:
		return "order missing"
	case AlreadyCancelled:
		return "order already cancelled"
	case OutsideCancellationWindow:
		return "outside cancellation window"
	default:
		return "unknown order error"
	}
}

type Offer struct {
	Available  bool
	PriceCents uint64
}

type Bill struct {
	OrderID    uint64
	PriceCents uint64
	DueAt      Timestamp
	Void       bool
}

// Order's zero value represents a missing order.
type Order struct {
	id       uint64
	sku      uint64
	placedAt Timestamp
	bill     Bill
}

func (order Order) ID() uint64 { return order.id }

//golean:export
func Search(sku uint64) Offer {
	if sku == 1 {
		return Offer{Available: true, PriceCents: 1250}
	}
	if sku == 2 {
		return Offer{PriceCents: 2400}
	}
	return Offer{}
}

//golean:export
func (order Order) Place(id, sku uint64, now, due Timestamp) (Order, OrderError) {
	if id == 0 {
		return order, InvalidID
	}
	if order.id != 0 {
		return order, AlreadyPlaced
	}
	offer := Search(sku)
	if !offer.Available || offer.PriceCents == 0 {
		return order, Unavailable
	}
	if due <= now {
		return order, InvalidDue
	}
	return Order{id: id, sku: sku, placedAt: now, bill: Bill{OrderID: id, PriceCents: offer.PriceCents, DueAt: due}}, OK
}

//golean:export
func (order Order) Cancel(now Timestamp) (Order, OrderError) {
	if order.id == 0 {
		return order, MissingOrder
	}
	if order.bill.Void {
		return order, AlreadyCancelled
	}
	if now < order.placedAt || order.bill.DueAt <= now {
		return order, OutsideCancellationWindow
	}
	order.bill.Void = true
	return order, OK
}

// Bill returns the original bill details even after cancellation.
//
//golean:export
func (order Order) Bill() (Bill, OrderError) {
	if order.id == 0 {
		return Bill{}, MissingOrder
	}
	return order.bill, OK
}

// Repository provides sequential order storage. Get returns the matching
// order or the zero Order when absent.
type Repository interface {
	//golean:assume matchesID : ∀ repo id, (Get repo id).«field:id» = id ∨ Get repo id = ⟨0, 0, 0, ⟨0, 0, 0, false⟩⟩
	Get(id uint64) Order
	Persist(order Order)
}

type Service struct {
	//golean:assume:initialized
	repo Repository
}

// NewService requires a valid repository.
//
//golean:verify:constructor
func NewService(repo Repository) Service {
	return Service{repo: repo}
}

//golean:boundary Repository.Get readonly
//golean:boundary Repository.Persist effect
//golean:verify placePersistsExactlyOnSuccess : ∀ {R : Type} (repo : InterfaceContracts.RepositoryContract R)
//golean:verify+   (service : Service R) (id sku : UInt64) (now due : Int64),
//golean:verify+   let transition := «Order$Place» (repo.Get service.«field:repo» id) id sku now due
//golean:verify+   «Service$Place» repo service id sku now due = (transition, Rules.persistence transition.2)
func (service Service) Place(id, sku uint64, now, due Timestamp) (Order, OrderError) {
	order := service.repo.Get(id)
	next, problem := order.Place(id, sku, now, due)
	if problem != OK {
		return next, problem
	}
	service.repo.Persist(next)
	return next, problem
}

//golean:boundary Repository.Get readonly
//golean:boundary Repository.Persist effect
//golean:verify cancelPersistsExactlyOnSuccess : ∀ {R : Type} (repo : InterfaceContracts.RepositoryContract R)
//golean:verify+   (service : Service R) (id : UInt64) (now : Int64),
//golean:verify+   let transition := «Order$Cancel» (repo.Get service.«field:repo» id) now
//golean:verify+   «Service$Cancel» repo service id now = (transition, Rules.persistence transition.2)
func (service Service) Cancel(id uint64, now Timestamp) (Order, OrderError) {
	order := service.repo.Get(id)
	next, problem := order.Cancel(now)
	if problem != OK {
		return next, problem
	}
	service.repo.Persist(next)
	return next, problem
}

//golean:boundary Repository.Get readonly
//golean:verify billHasNoEffects : ∀ {R : Type} (repo : InterfaceContracts.RepositoryContract R)
//golean:verify+   (service : Service R) (id : UInt64),
//golean:verify+   «Service$GetBill» repo service id = («Order$Bill» (repo.Get service.«field:repo» id), [])
func (service Service) GetBill(id uint64) (Bill, OrderError) {
	return service.repo.Get(id).Bill()
}
