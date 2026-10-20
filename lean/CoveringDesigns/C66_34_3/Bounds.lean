import CoveringDesigns.TwoKMinusTwoCapacity.Exactness

namespace CoveringDesigns.C66_34_3

/-- Exact fourteen on arbitrary sixty-six-point labels. -/
theorem exactness_on {α : Type*} [Fintype α] (hv : Fintype.card α = 66) :
    (∃ C : Family α, IsCover C 34 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C 34 3 → 14 ≤ C.card) :=
  TwoKMinusTwoCapacity.exactness (k := 34) (by omega) (by norm_num)

end CoveringDesigns.C66_34_3
