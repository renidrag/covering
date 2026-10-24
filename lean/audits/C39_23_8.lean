import CoveringDesigns.C39_23_8

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_39_23_8 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 39 → IsCover C 23 8 → 229 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_39_23_8
#print axioms CoveringDesigns.lower_bound_39_23_8

namespace CoveringDesigns.Audit39_23_8

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 39)
    (hsize : ∀ B ∈ C, B.card = 23)
    (hcover : ∀ T : Finset α, T.card = 8 → ∃ B ∈ C, T ⊆ B) :
    229 ≤ C.card := lower_bound_39_23_8 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit39_23_8

#guard_standard_axioms CoveringDesigns.Audit39_23_8.lower_bound_explicit
#print axioms CoveringDesigns.Audit39_23_8.lower_bound_explicit
