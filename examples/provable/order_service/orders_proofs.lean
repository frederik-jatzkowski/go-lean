import order_service.orders_laws

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/order_service».orders.Proofs

theorem searchMatchesRules : Laws.searchMatchesRules := by
  intro sku
  simp [Search, Rules.search]

theorem placeMatchesRules : Laws.placeMatchesRules := by
  intro order id sku now due
  by_cases invalidID : id = 0
  · simp [«Order$Place», Rules.place, invalidID]
  by_cases placed : order.«field:id» = 0
  · by_cases available : sku = 1
    · simp [«Order$Place», Search, Rules.place, invalidID, placed, available]
    · simp [«Order$Place», Search, Rules.place, invalidID, placed, available]
      split <;> simp
  · simp [«Order$Place», Rules.place, invalidID, placed]

theorem cancelMatchesRules : Laws.cancelMatchesRules := by
  intro order now
  by_cases missing : order.«field:id» = 0
  · simp [«Order$Cancel», Rules.cancel, missing]
  by_cases void : order.«field:bill».«field:Void» = true
  · simp [«Order$Cancel», Rules.cancel, missing, void]
  by_cases early : now < order.«field:placedAt»
  · simp [«Order$Cancel», Rules.cancel, missing, void, early]
  · simp [«Order$Cancel», Rules.cancel, missing, void, early]

theorem billMatchesRules : Laws.billMatchesRules := by
  intro order
  simp [«Order$Bill», Rules.bill, Rules.emptyBill]

private theorem stepMatches (order : Order) (command : Rules.Command) :
    Rules.applyGo order command = Rules.applySpec order command := by
  cases command with
  | place id sku now due => exact placeMatchesRules order id sku now due
  | cancel now => exact cancelMatchesRules order now

theorem rejectionPreservesOrder : Laws.rejectionPreservesOrder := by
  intro order command
  rw [stepMatches]
  cases command <;> simp only [Rules.applySpec, Rules.place, Rules.cancel] <;>
    (repeat' first | split | (simp_all <;> done))

private theorem runMatches (order : Order) (commands : List Rules.Command) :
    Rules.run Rules.applyGo order commands = Rules.run Rules.applySpec order commands := by
  induction commands generalizing order with
  | nil => rfl
  | cons command commands ih => simp only [Rules.run, stepMatches order command, ih]

theorem historiesMatchRules : Laws.historiesMatchRules := by
  exact runMatches Rules.emptyOrder

private theorem stepValid (order : Order) (command : Rules.Command) (valid : Rules.Valid order) :
    Rules.Valid (Rules.applySpec order command).1 := by
  cases command with
  | place id sku now due =>
    simp only [Rules.applySpec, Rules.place]
    split
    · exact valid
    split
    · exact valid
    split
    · exact valid
    split
    · exact valid
    rename_i nonzero _ skuAvailable validDue
    exact Or.inr ⟨nonzero, Classical.byContradiction skuAvailable, rfl, rfl, validDue⟩
  | cancel now =>
    simp only [Rules.applySpec, Rules.cancel]
    split
    · exact valid
    split
    · exact valid
    split
    · exact valid
    rename_i present _ _
    rcases valid with empty | issued
    · exact False.elim (present (congrArg Order.«field:id» empty))
    · exact Or.inr issued

private theorem runValid (order : Order) (commands : List Rules.Command) (valid : Rules.Valid order) :
    Rules.Valid (Rules.run Rules.applySpec order commands).1 := by
  induction commands generalizing order with
  | nil => exact valid
  | cons command commands ih =>
    exact ih _ (stepValid order command valid)

theorem historiesPreserveValidity : Laws.historiesPreserveValidity := by
  intro commands
  rw [historiesMatchRules commands]
  exact runValid Rules.emptyOrder commands (Or.inl rfl)

theorem placePersistsExactlyOnSuccess : Laws.placePersistsExactlyOnSuccess := by
  intro R repo service id sku now due
  cases transition : «Order$Place» (repo.Get service.«field:repo» id) id sku now due with
  | mk next problem =>
    by_cases success : problem = 0 <;>
      simp [«Service$Place», Rules.persistence, transition, success]

theorem cancelPersistsExactlyOnSuccess : Laws.cancelPersistsExactlyOnSuccess := by
  intro R repo service id now
  cases transition : «Order$Cancel» (repo.Get service.«field:repo» id) now with
  | mk next problem =>
    by_cases success : problem = 0 <;>
      simp [«Service$Cancel», Rules.persistence, transition, success]

theorem billHasNoEffects : Laws.billHasNoEffects := by
  intro R repo service id
  rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/order_service».orders.Proofs
