package local_array_loop

//golean:verify marksExactly : ∀ (slots : List GoTypes.Int), (slots.length : Int) < 2 ^ (GoTypes.WordBits - 1) →
//golean:verify+   (∀ slot ∈ slots, 0 ≤ slot.toInt ∧ slot.toInt < 30) →
//golean:verify+   ∃ out, markOccupied slots = some out ∧
//golean:verify+     ∀ i : Fin 30, out[i] = true ↔ ∃ slot ∈ slots, slot.toInt = i.val
//golean:verify badSlotPanics : ∀ (slots : List GoTypes.Int), (slots.length : Int) < 2 ^ (GoTypes.WordBits - 1) →
//golean:verify+   (∃ slot ∈ slots, slot.toInt < 0 ∨ 30 ≤ slot.toInt) → markOccupied slots = none
func markOccupied(slots []int) [30]bool {
	var occupied [30]bool
	for _, slot := range slots {
		occupied[slot] = true
	}
	return occupied
}

//golean:verify seesCurrentState : ∀ (slots : List GoTypes.Int), (slots.length : Int) < 2 ^ (GoTypes.WordBits - 1) →
//golean:verify+   (∀ slot ∈ slots, 0 ≤ slot.toInt ∧ slot.toInt < 30) →
//golean:verify+   observeAndClear slots = some (Vector.replicate 30 false, true)
func observeAndClear(slots []int) ([30]bool, bool) {
	var occupied [30]bool
	allObserved := true
	for _, slot := range slots {
		occupied[slot] = true
		if !isOccupied(occupied, slot) {
			allObserved = false
		}
		occupied[slot] = false
	}
	return occupied, allObserved
}

//golean:verify readsSlot : ∀ (occupied : Vector Bool 30) (slot : GoTypes.Int) (h : 0 ≤ slot.toInt)
//golean:verify+   (hi : slot.toInt < 30),
//golean:verify+   isOccupied occupied slot = some (occupied.get ⟨slot.toInt.toNat, by omega⟩)
func isOccupied(occupied [30]bool, slot int) bool {
	return occupied[slot]
}
