# Order service

The order service separates value transitions from repository calls. `Order.Place` and `Order.Cancel` return an order and a domain rejection code. `Service.Place` and `Service.Cancel` read an order, apply the transition, and persist the result on success. The example proves both the domain behavior and the service's decision to invoke persistence. [Go implementation](../examples/provable/order_service/orders.go)

## Follow an order

1. The zero `Order` represents a missing order. `Search(1)` returns an available offer priced at 1,250 cents. SKU 2 has a listed price and is unavailable. Other SKUs return the zero offer.
2. Placing order 7 for SKU 1 succeeds if the order is missing and the supplied due timestamp is strictly after placement. The method constructs a bill with the order ID, price, and due time. When several placement checks could fail, the returned code follows the check order in the method: invalid ID, already placed, unavailable, then invalid due date.
3. Cancellation is allowed from the placement timestamp inclusive to the due timestamp exclusive. At `due - 1` it can succeed and set the bill's `Void` flag. At `due` it fails when the order is otherwise eligible for cancellation. A later bill lookup still returns the original bill details with the void flag set after a successful cancellation.

The runnable demo supplies Unix microsecond timestamps and stores orders in a map. It places order 7, reads its bill, cancels just before the deadline, and reads the void bill. [Demo source](../examples/provable/order_service/cmd/orders/main.go)

## Prove the domain transitions

[orders_rules.lean](../examples/provable/order_service/orders_rules.lean) describes search, placement, cancellation, and bill lookup using generated types. The specification builds the expected order and chooses the rejection code from the rules. The package comment in `orders.go` imports this specification and declares laws over the functions and methods selected with `export`.

In [orders_proofs.lean](../examples/provable/order_service/orders_proofs.lean), `placeMatchesRules` and `cancelMatchesRules` establish equality of the entire returned order and rejection code. `rejectionPreservesOrder` shows that any rejected domain command returns the original order. `runMatches` lifts single-step agreement by induction over any finite list of placement and cancellation commands. From the empty order, `historiesMatchRules` gives agreement on the final state and every transition result, including rejections.

`historiesPreserveValidity` uses a second induction to show that the final state is empty or has a nonzero ID, SKU 1, a bill with the same ID and a 1,250-cent price, and a due time after placement. These histories thread an order value through domain commands.

## Prove the persistence decision

`Repository.Get` carries a law that it returns an order with the requested ID or the zero order. The `Service.repo` field is marked initialized, and the constructor check establishes initialization from a valid repository input. The service methods classify `Get` as read-only and `Persist` as an effect.

In the generated model, `Service$Place` takes a `RepositoryContract` and returns `(Order × UInt8) × List String`. The `UInt8` represents the Go `OrderError`. `placePersistsExactlyOnSuccess` and `cancelPersistsExactlyOnSuccess` equate the ordinary result to the corresponding domain transition on the fetched order. The trace contains one qualified `Repository.Persist` entry on success and is empty on rejection. `billHasNoEffects` gives the bill lookup result and an empty trace. [Generated model](../examples/provable/order_service/orders_gen.lean)

The trace records method invocations. Applying the theorem to a real service requires a valid repository, a read-only `Get` that meets its return-value contract, and normal execution of the modeled calls. Storage durability and concurrency depend on the repository implementation. The [Go tests](../examples/provable/order_service/orders_test.go) exercise the service with test repositories.

[Run the demo and its checks from a checkout](../CONTRIBUTING.md#run-and-check-the-order-service).
