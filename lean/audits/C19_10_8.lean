import CoveringDesigns.C19_10_8

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_19_10_8 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 19 → IsCover C 10 8 → 1908 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_19_10_8
#print axioms CoveringDesigns.lower_bound_19_10_8

namespace CoveringDesigns.Audit19_10_8

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 19)
    (hsize : ∀ B ∈ C, B.card = 10)
    (hcover : ∀ T : Finset α, T.card = 8 → ∃ B ∈ C, T ⊆ B) :
    1908 ≤ C.card := lower_bound_19_10_8 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit19_10_8

#guard_standard_axioms CoveringDesigns.Audit19_10_8.lower_bound_explicit
#print axioms CoveringDesigns.Audit19_10_8.lower_bound_explicit
