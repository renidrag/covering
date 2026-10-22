import CoveringDesigns.QuadrupleAssembly.Applications
import CoveringDesigns.QuadrupleAssembly.SmallCases

/-! Completion of the admissible n≡1 (mod 12) range below 100.
This finite theorem supplies no all-order seed-existence assertion.
Formalisation: Rob Gardiner, with AI assistance. -/

namespace CoveringDesigns

namespace QuadrupleAssembly

theorem admissible_below_100_iff (n : ℕ) :
    (4 ≤ n ∧ n < 100 ∧ n % 12 = 1) ↔
    (n = 13 ∨ n = 25 ∨ n = 37 ∨ n = 49 ∨ n = 61 ∨ n = 73 ∨ n = 85 ∨ n = 97) := by
  omega

/-- The displayed quotient is exact natural-number division in this range. -/
theorem formula_divisible_below_100 {n : ℕ}
    (hn : 4 ≤ n) (h100 : n < 100) (hmod : n % 12 = 1) :
    24 ∣ n * (n-1)^2 := by
  rcases (admissible_below_100_iff n).mp ⟨hn,h100,hmod⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end QuadrupleAssembly

/-- All eight classical exact values, for arbitrary finite labels and ordinary
families. The lower admissibility bound excludes n=1. -/
theorem covering_number_one_mod_twelve_below_100_on
    {α : Type*} [Fintype α] {n : ℕ} (hv : Fintype.card α = n)
    (hn : 4 ≤ n) (h100 : n < 100) (hmod : n % 12 = 1) :
    (∃ C : Family α, IsCover C 4 3 ∧ C.card = n * (n-1)^2 / 24) ∧
    (∀ C : Family α, IsCover C 4 3 → n * (n-1)^2 / 24 ≤ C.card) := by
  rcases (QuadrupleAssembly.admissible_below_100_iff n).mp ⟨hn,h100,hmod⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covering_number_13_4_3_on hv
  · exact covering_number_25_4_3_on hv
  · exact covering_number_37_4_3_on hv
  · exact covering_number_49_4_3_on hv
  · exact covering_number_61_4_3_on hv
  · exact covering_number_73_4_3_on hv
  · exact covering_number_85_4_3_on hv
  · exact covering_number_97_4_3_on hv

theorem covering_number_one_mod_twelve_below_100 {n : ℕ}
    (hn : 4 ≤ n) (h100 : n < 100) (hmod : n % 12 = 1) :
    (∃ C : Family (Fin n), IsCover C 4 3 ∧ C.card = n * (n-1)^2 / 24) ∧
    (∀ C : Family (Fin n), IsCover C 4 3 → n * (n-1)^2 / 24 ≤ C.card) :=
  covering_number_one_mod_twelve_below_100_on (Fintype.card_fin n) hn h100 hmod

end CoveringDesigns
