import batch_fulfillment.batch_fulfillment_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/batch_fulfillment».batch_fulfillment.Proofs

private def orders (batch : Batch) : List Order := batch.«field:orders».getD []

private def debit (batch : Batch) (order : Order) : Batch :=
  { batch with
    «field:stock» := batch.«field:stock» - order.«field:Quantity»
    «field:cursor» := batch.«field:cursor» + 1 }

-- A shipment accounts for exactly the orders at successive cursor positions.
inductive ShippedPrefix (pending : List Order) : Int64 → Int64 → List Int → Prop where
  | stop (cursor) : ShippedPrefix pending cursor cursor []
  | ship (cursor finish : Int64) (order : Order) (rest : List Int)
      (atCursor : pending[cursor.toNatClampNeg]? = some order)
      (positive : 0 < order.«field:Quantity»)
      (tail : ShippedPrefix pending (cursor + 1) finish rest) :
      ShippedPrefix pending cursor finish (order.«field:Quantity».toInt :: rest)

private theorem fulfillStep (batch : Batch) (fuel : Nat) :
    «Batch$Fulfill$loop» (some batch) (fuel + 1) =
      if batch.«field:cursor» < Int64.ofNat (orders batch).length then
        if batch.«field:cursor».toInt < 0 then none else
          match (orders batch)[batch.«field:cursor».toNatClampNeg]? with
          | none => none
          | some order =>
            if order.«field:Quantity» ≤ 0 ∨ batch.«field:stock» < order.«field:Quantity» then
              some (some batch, true)
            else «Batch$Fulfill$loop» (some (debit batch order)) fuel
      else some (some batch, false) := by
  by_cases guard : batch.«field:cursor» < Int64.ofNat (batch.«field:orders».getD []).length
  · by_cases negative : batch.«field:cursor».toInt < 0
    · simp [«Batch$Fulfill$loop», orders, guard, negative, bind, Option.bind, Option.map]
    · cases index : (batch.«field:orders».getD [])[batch.«field:cursor».toNatClampNeg]? with
      | none => simp [«Batch$Fulfill$loop», orders, guard, negative, index, bind, Option.bind, Option.map]
      | some order =>
        by_cases positive : order.«field:Quantity» ≤ 0
        · simp [«Batch$Fulfill$loop», orders, guard, negative, index, positive, bind, Option.bind, Option.map]
        · by_cases stock : batch.«field:stock» < order.«field:Quantity» <;>
            simp [«Batch$Fulfill$loop», orders, guard, negative, index, positive, stock,
              debit, bind, Option.bind, Option.map]
  · simp [«Batch$Fulfill$loop», orders, guard, bind, Option.bind, Option.map]

private theorem accounting (fuel : Nat) (batch final : Batch) (rejected : Bool)
    (nonnegative : 0 ≤ batch.«field:stock»)
    (result : «Batch$Fulfill$loop» (some batch) fuel = some (some final, rejected)) :
    final.«field:orders» = batch.«field:orders» ∧ 0 ≤ final.«field:stock» ∧
      ∃ shipped, ShippedPrefix (orders batch) batch.«field:cursor» final.«field:cursor» shipped ∧
        batch.«field:stock».toInt = final.«field:stock».toInt + shipped.sum := by
  induction fuel generalizing batch with
  | zero => simp [«Batch$Fulfill$loop»] at result
  | succ fuel ih =>
    have stopped (same : batch = final) :
        final.«field:orders» = batch.«field:orders» ∧ 0 ≤ final.«field:stock» ∧
          ∃ shipped, ShippedPrefix (orders batch) batch.«field:cursor» final.«field:cursor» shipped ∧
            batch.«field:stock».toInt = final.«field:stock».toInt + shipped.sum := by
      subst final
      exact ⟨rfl, nonnegative, [], .stop _, by simp⟩
    rw [fulfillStep] at result
    simp only [orders] at result
    by_cases guard : batch.«field:cursor» < Int64.ofNat (batch.«field:orders».getD []).length
    · by_cases negative : batch.«field:cursor».toInt < 0
      · simp [guard, negative] at result
      · cases index : (batch.«field:orders».getD [])[batch.«field:cursor».toNatClampNeg]? with
        | none => simp [guard, negative, index] at result
        | some order =>
          by_cases reject : order.«field:Quantity» ≤ 0 ∨ batch.«field:stock» < order.«field:Quantity»
          · simp [guard, negative, index, reject] at result
            exact stopped result.1
          · simp only [guard, negative, index, reject, ite_true, ite_false] at result
            have positive : 0 < order.«field:Quantity» := Int64.not_le.mp (fun h => reject (.inl h))
            have enough : order.«field:Quantity» ≤ batch.«field:stock» :=
              Int64.not_lt.mp (fun h => reject (.inr h))
            have subtraction := Int64.toInt_sub_of_le _ _ (Int64.le_of_lt positive) enough
            have nonnegativeDebit : 0 ≤ (debit batch order).«field:stock» :=
              Int64.sub_nonneg_of_le (Int64.le_of_lt positive) enough
            obtain ⟨route, stock, shipped, shippedPrefix, sum⟩ := ih (debit batch order) nonnegativeDebit result
            refine ⟨route, stock, order.«field:Quantity».toInt :: shipped, .ship _ _ order shipped index positive shippedPrefix, ?_⟩
            simp only [debit, subtraction] at sum
            simp only [List.sum_cons]
            omega
    · simp [guard] at result
      exact stopped result.1

private theorem entryFuel (batch : Batch) :
    «Batch$Fulfill» (some batch) = «Batch$Fulfill$loop» (some batch)
      (((Int64.ofNat (batch.«field:orders».getD []).length).toInt -
        batch.«field:cursor».toInt).toNat + 1) := by rfl

private theorem shippedPrefixChecks {pending : List Order} {start finish : Int64} {shipped : List Int}
    (path : ShippedPrefix pending start finish shipped) :
    shipped.foldr (fun quantity tail cursor =>
      ∃ order : Order, pending[cursor.toNatClampNeg]? = some order ∧
        0 < order.«field:Quantity» ∧ quantity = order.«field:Quantity».toInt ∧ tail (cursor + 1))
      (fun cursor => cursor = finish) start := by
  induction path with
  | stop => rfl
  | ship _ _ order _ atCursor positive _ ih =>
    exact ⟨order, atCursor, positive, rfl, ih⟩

theorem nonnegativeAndConservesStock : Laws.nonnegativeAndConservesStock := by
  intro batch final rejected nonnegative result
  rw [entryFuel] at result
  obtain ⟨ordersUnchanged, stock, shipped, path, sum⟩ := accounting _ batch final rejected nonnegative result
  exact ⟨ordersUnchanged, stock, shipped, shippedPrefixChecks path, sum⟩

theorem rejectedOrderStaysAtTheCursor : Laws.rejectedOrderStaysAtTheCursor := by rfl

theorem resumedBatchProcessesPreviouslyRejectedOrder : Laws.resumedBatchProcessesPreviouslyRejectedOrder := by rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/batch_fulfillment».batch_fulfillment.Proofs
