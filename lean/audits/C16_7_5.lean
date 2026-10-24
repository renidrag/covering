import CoveringDesigns.C16_7_5

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_16_7_5 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 16 → IsCover C 7 5 → 236 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_16_7_5
#print axioms CoveringDesigns.lower_bound_16_7_5

namespace CoveringDesigns.Audit16_7_5

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 16)
    (hsize : ∀ B ∈ C, B.card = 7)
    (hcover : ∀ T : Finset α, T.card = 5 → ∃ B ∈ C, T ⊆ B) :
    236 ≤ C.card := lower_bound_16_7_5 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit16_7_5

#guard_standard_axioms CoveringDesigns.Audit16_7_5.lower_bound_explicit
#print axioms CoveringDesigns.Audit16_7_5.lower_bound_explicit
