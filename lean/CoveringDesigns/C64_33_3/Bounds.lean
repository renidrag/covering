import CoveringDesigns.TwoKMinusTwoCapacity.Exactness

namespace CoveringDesigns.C64_33_3

/-- Exact fourteen on arbitrary sixty-four-point labels. -/
theorem exactness_on {α : Type*} [Fintype α] (hv : Fintype.card α = 64) :
    (∃ C : Family α, IsCover C 33 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C 33 3 → 14 ≤ C.card) :=
  TwoKMinusTwoCapacity.exactness (k := 33) (by omega) (by norm_num)

end CoveringDesigns.C64_33_3
