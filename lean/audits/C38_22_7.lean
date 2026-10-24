import CoveringDesigns.C38_22_7

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_38_22_7 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 38 → IsCover C 22 7 → 135 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_38_22_7
#print axioms CoveringDesigns.lower_bound_38_22_7

namespace CoveringDesigns.Audit38_22_7

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 38)
    (hsize : ∀ B ∈ C, B.card = 22)
    (hcover : ∀ T : Finset α, T.card = 7 → ∃ B ∈ C, T ⊆ B) :
    135 ≤ C.card := lower_bound_38_22_7 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit38_22_7

#guard_standard_axioms CoveringDesigns.Audit38_22_7.lower_bound_explicit
#print axioms CoveringDesigns.Audit38_22_7.lower_bound_explicit
