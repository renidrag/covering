import CoveringDesigns.C37_21_6

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_37_21_6 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 37 → IsCover C 21 6 → 78 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_37_21_6
#print axioms CoveringDesigns.lower_bound_37_21_6

namespace CoveringDesigns.Audit37_21_6

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 37)
    (hsize : ∀ B ∈ C, B.card = 21)
    (hcover : ∀ T : Finset α, T.card = 6 → ∃ B ∈ C, T ⊆ B) :
    78 ≤ C.card := lower_bound_37_21_6 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit37_21_6

#guard_standard_axioms CoveringDesigns.Audit37_21_6.lower_bound_explicit
#print axioms CoveringDesigns.Audit37_21_6.lower_bound_explicit
