import CoveringDesigns.TwoKMinusCGeneral.UniformLower
import CoveringDesigns.TwoKMinusCGeneral.OffsetThreeLower
import CoveringDesigns.TwoKMinusCGeneral.Attainment

/-! Exact ordinary coverings, with arbitrary labels and concrete applications. -/
namespace CoveringDesigns.TwoKMinusCGeneral
variable {α : Type*} [Fintype α] {c k : ℕ}

theorem exists_fourteen_uniform (hv : Fintype.card α=2*k-c) (hc : 2≤c) (hk : 25*c≤k) :
    ∃ C : Family α, IsCover C k 3 ∧ C.card=14 := by
  obtain ⟨C,hC,hb⟩ := upper_bound (α := α) (c := c) (k := k) (by omega) hc (by omega) (by omega)
  exact ⟨C,hC,Nat.le_antisymm hb (fourteen_le_card_uniform hv hc hk hC)⟩

theorem exactness_uniform (hv : Fintype.card α=2*k-c) (hc : 2≤c) (hk : 25*c≤k) :
    (∃ C : Family α, IsCover C k 3 ∧ C.card=14) ∧
    (∀ C : Family α, IsCover C k 3 → 14≤C.card) :=
  ⟨exists_fourteen_uniform hv hc hk,fun _ h => fourteen_le_card_uniform hv hc hk h⟩

theorem covering_number_uniform (hc : 2≤c) (hk : 25*c≤k) :
    (∃ C : Family (Fin (2*k-c)), IsCover C k 3 ∧ C.card=14) ∧
    (∀ C : Family (Fin (2*k-c)), IsCover C k 3 → 14≤C.card) :=
  exactness_uniform (by simp) hc hk

theorem exists_fourteen_offset_three (hv : Fintype.card α=2*k-3) (hk : 59≤k) :
    ∃ C : Family α, IsCover C k 3 ∧ C.card=14 := by
  obtain ⟨C,hC,hb⟩ := upper_bound (α := α) (c := 3) (k := k) (by omega) (by decide) (by omega) (by omega)
  exact ⟨C,hC,Nat.le_antisymm hb (fourteen_le_card_offset_three hv hk hC)⟩

theorem exactness_offset_three (hv : Fintype.card α=2*k-3) (hk : 59≤k) :
    (∃ C : Family α, IsCover C k 3 ∧ C.card=14) ∧
    (∀ C : Family α, IsCover C k 3 → 14≤C.card) :=
  ⟨exists_fourteen_offset_three hv hk,fun _ h => fourteen_le_card_offset_three hv hk h⟩

theorem covering_number_offset_three (hk : 59≤k) :
    (∃ C : Family (Fin (2*k-3)), IsCover C k 3 ∧ C.card=14) ∧
    (∀ C : Family (Fin (2*k-3)), IsCover C k 3 → 14≤C.card) :=
  exactness_offset_three (by simp) hk

theorem exactness_98_50_3_on (hv : Fintype.card α=98) :
    (∃ C : Family α, IsCover C 50 3 ∧ C.card=14) ∧
    (∀ C : Family α, IsCover C 50 3 → 14≤C.card) :=
  exactness_uniform (c := 2) (by omega) (by decide) (by decide)

theorem exactness_196_100_3_on (hv : Fintype.card α=196) :
    (∃ C : Family α, IsCover C 100 3 ∧ C.card=14) ∧
    (∀ C : Family α, IsCover C 100 3 → 14≤C.card) :=
  exactness_uniform (c := 4) (by omega) (by decide) (by decide)

theorem exactness_115_59_3_on (hv : Fintype.card α=115) :
    (∃ C : Family α, IsCover C 59 3 ∧ C.card=14) ∧
    (∀ C : Family α, IsCover C 59 3 → 14≤C.card) :=
  exactness_offset_three (by omega) (by decide)

end CoveringDesigns.TwoKMinusCGeneral
