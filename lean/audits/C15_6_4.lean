import CoveringDesigns.C15_6_4

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_15_6_4 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 15 → IsCover C 6 4 → 103 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_15_6_4
#print axioms CoveringDesigns.lower_bound_15_6_4

namespace CoveringDesigns.Audit15_6_4

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 15)
    (hsize : ∀ B ∈ C, B.card = 6)
    (hcover : ∀ T : Finset α, T.card = 4 → ∃ B ∈ C, T ⊆ B) :
    103 ≤ C.card := lower_bound_15_6_4 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit15_6_4

#guard_standard_axioms CoveringDesigns.Audit15_6_4.lower_bound_explicit
#print axioms CoveringDesigns.Audit15_6_4.lower_bound_explicit
