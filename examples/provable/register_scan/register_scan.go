package register_scan

//golean:verify selectsHighestFree : ∀ (occupied : Vector Bool 30), ∃ result : GoTypes.Int,
//golean:verify+   freeRegister occupied = some result ∧
//golean:verify+   (result = -1 ↔ ∀ i : Fin 30, occupied[i] = true) ∧
//golean:verify+   (result ≠ -1 → ∃ i : Fin 30, result.toInt = i.val ∧ occupied[i] = false ∧
//golean:verify+     ∀ j : Fin 30, i < j → occupied[j] = true)
func freeRegister(occupied [30]bool) int {
	result := -1
	for slot := 0; slot < 30; slot++ {
		if !occupied[slot] {
			result = slot
		}
	}
	return result
}
