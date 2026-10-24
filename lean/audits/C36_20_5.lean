import CoveringDesigns.C36_20_5

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_36_20_5 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 36 → IsCover C 20 5 → 44 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_36_20_5
#print axioms CoveringDesigns.lower_bound_36_20_5

namespace CoveringDesigns.Audit36_20_5

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 36)
    (hsize : ∀ B ∈ C, B.card = 20)
    (hcover : ∀ T : Finset α, T.card = 5 → ∃ B ∈ C, T ⊆ B) :
    44 ≤ C.card := lower_bound_36_20_5 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit36_20_5

#guard_standard_axioms CoveringDesigns.Audit36_20_5.lower_bound_explicit
#print axioms CoveringDesigns.Audit36_20_5.lower_bound_explicit
