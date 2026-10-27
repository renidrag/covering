import CoveringDesigns.C4k_K_2

namespace CoveringDesigns.C4k_K_2.Examples

theorem c32_8_2 :
    (∃ C : Family (Fin 32), IsCover C 8 2 ∧ C.card = 20) ∧
    (∀ C : Family (Fin 32), IsCover C 8 2 → 20 ≤ C.card) := by
  simpa using covering_number (k := 8) (by decide)

theorem c36_9_2 :
    (∃ C : Family (Fin 36), IsCover C 9 2 ∧ C.card = 21) ∧
    (∀ C : Family (Fin 36), IsCover C 9 2 → 21 ≤ C.card) := by
  simpa using covering_number (k := 9) (by decide)

theorem c40_10_2 :
    (∃ C : Family (Fin 40), IsCover C 10 2 ∧ C.card = 21) ∧
    (∀ C : Family (Fin 40), IsCover C 10 2 → 21 ≤ C.card) := by
  simpa using covering_number (k := 10) (by decide)

theorem c44_11_2 :
    (∃ C : Family (Fin 44), IsCover C 11 2 ∧ C.card = 21) ∧
    (∀ C : Family (Fin 44), IsCover C 11 2 → 21 ≤ C.card) := by
  simpa using covering_number (k := 11) (by decide)

theorem c60_15_2 :
    (∃ C : Family (Fin 60), IsCover C 15 2 ∧ C.card = 21) ∧
    (∀ C : Family (Fin 60), IsCover C 15 2 → 21 ≤ C.card) := by
  simpa using covering_number (k := 15) (by decide)

end CoveringDesigns.C4k_K_2.Examples
