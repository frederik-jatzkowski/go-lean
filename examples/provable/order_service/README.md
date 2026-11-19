# Verified order service

From the repository root, run the example and check its proofs.

```sh
go run ./examples/provable/order_service/cmd/orders
lake build order_service.orders_verify
```

The example searches the catalog, places one order, looks up its bill, and cancels
one microsecond before the deadline. The next bill lookup returns the same
billing details with the void flag set.

`Order` is a value entity. Its commands return the updated order on success or
the original order and a domain error code on rejection. The service loads the
entity through `Get(id) Order` and invokes `Persist(order)` once on success. Use
a valid repository with `NewService`. The demo uses a sequential in-memory map.

The verified API accepts signed Unix timestamps in microseconds. Convert a Go
`time.Time` at the boundary with `Timestamp(t.UnixMicro())` for instants within
range. Cancellation accepts timestamps from placement inclusive to the deadline
exclusive. The caller supplies the wall-clock time and deadline.

Lean checks that search, placement, billing, and cancellation agree with the
reference rules. It checks the invariant and the complete sequence of command
results for every finite placement and cancellation history from an empty
order. For every loaded entity, it checks that the application service returns
the entity result, produces an empty persistence trace on rejection, and
invokes `Persist` exactly once on success. Go tests check the complete payload
sent to the recording repository.

The service theorems assume initialized dependencies, a read-only `Get` that
returns the matching order or the zero value, and normally returning repository
calls. The trace describes calls to the port. The example uses a read-only
catalog snapshot, a single unit per order, and no payment or stock reservation.
