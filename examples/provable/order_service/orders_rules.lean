import order_service.orders_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/order_service».orders.Rules

def emptyBill : Bill := ⟨0, 0, 0, false⟩

def emptyOrder : Order := ⟨0, 0, 0, emptyBill⟩

def search (sku : UInt64) : Offer :=
  if sku = 1 then ⟨true, 1250⟩ else if sku = 2 then ⟨false, 2400⟩ else ⟨false, 0⟩

def place (order : Order) (id sku : UInt64) (now due : Int64) : Order × UInt8 :=
  if id = 0 then (order, 1)
  else if order.«field:id» ≠ 0 then (order, 2)
  else if sku ≠ 1 then (order, 3)
  else if due ≤ now then (order, 4)
  else (⟨id, sku, now, ⟨id, 1250, due, false⟩⟩, 0)

def cancel (order : Order) (now : Int64) : Order × UInt8 :=
  if order.«field:id» = 0 then (order, 5)
  else if order.«field:bill».«field:Void» then (order, 6)
  else if now < order.«field:placedAt» ∨ order.«field:bill».«field:DueAt» ≤ now then (order, 7)
  else ({ order with «field:bill» := { order.«field:bill» with «field:Void» := true } }, 0)

def bill (order : Order) : Bill × UInt8 :=
  if order.«field:id» = 0 then (emptyBill, 5) else (order.«field:bill», 0)

def persistence (problem : UInt8) : List String :=
  if problem = 0 then ["github.com/frederik-jatzkowski/go-lean/examples/provable/order_service.Repository.Persist"]
  else []

inductive Command where
  | place (id sku : UInt64) (now due : Int64)
  | cancel (now : Int64)

def applyGo (order : Order) : Command → Order × UInt8
  | .place id sku now due => «Order$Place» order id sku now due
  | .cancel now => «Order$Cancel» order now

def applySpec (order : Order) : Command → Order × UInt8
  | .place id sku now due => place order id sku now due
  | .cancel now => cancel order now

def run (step : Order → Command → Order × UInt8) (order : Order) :
    List Command → Order × List (Order × UInt8)
  | [] => (order, [])
  | command :: commands =>
    let transition := step order command
    let (final, results) := run step transition.1 commands
    (final, transition :: results)

def Valid (order : Order) : Prop :=
  order = emptyOrder ∨
    (order.«field:id» ≠ 0 ∧ order.«field:sku» = 1 ∧
      order.«field:bill».«field:OrderID» = order.«field:id» ∧
      order.«field:bill».«field:PriceCents» = 1250 ∧
      ¬ order.«field:bill».«field:DueAt» ≤ order.«field:placedAt»)

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/order_service».orders.Rules
