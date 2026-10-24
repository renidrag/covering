import CoveringDesigns.C18_9_7

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_18_9_7 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 18 → IsCover C 9 7 → 1004 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_18_9_7
#print axioms CoveringDesigns.lower_bound_18_9_7

namespace CoveringDesigns.Audit18_9_7

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 18)
    (hsize : ∀ B ∈ C, B.card = 9)
    (hcover : ∀ T : Finset α, T.card = 7 → ∃ B ∈ C, T ⊆ B) :
    1004 ≤ C.card := lower_bound_18_9_7 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit18_9_7

#guard_standard_axioms CoveringDesigns.Audit18_9_7.lower_bound_explicit
#print axioms CoveringDesigns.Audit18_9_7.lower_bound_explicit
