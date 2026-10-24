import CoveringDesigns.C35_19_4

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_35_19_4 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 35 → IsCover C 19 4 → 24 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_35_19_4
#print axioms CoveringDesigns.lower_bound_35_19_4

namespace CoveringDesigns.Audit35_19_4

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 35)
    (hsize : ∀ B ∈ C, B.card = 19)
    (hcover : ∀ T : Finset α, T.card = 4 → ∃ B ∈ C, T ⊆ B) :
    24 ≤ C.card := lower_bound_35_19_4 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit35_19_4

#guard_standard_axioms CoveringDesigns.Audit35_19_4.lower_bound_explicit
#print axioms CoveringDesigns.Audit35_19_4.lower_bound_explicit
