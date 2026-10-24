import CoveringDesigns.C17_8_6

/-! Universal arbitrary-label contract and expanded ordinary covering condition. -/
open CoveringDesigns
universe u

#check (@CoveringDesigns.lower_bound_17_8_6 : ∀ {α : Type u} [Fintype α] {C : Family α},
    Fintype.card α = 17 → IsCover C 8 6 → 502 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_17_8_6
#print axioms CoveringDesigns.lower_bound_17_8_6

namespace CoveringDesigns.Audit17_8_6

theorem lower_bound_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 17)
    (hsize : ∀ B ∈ C, B.card = 8)
    (hcover : ∀ T : Finset α, T.card = 6 → ∃ B ∈ C, T ⊆ B) :
    502 ≤ C.card := lower_bound_17_8_6 hv ⟨hsize, hcover⟩

end CoveringDesigns.Audit17_8_6

#guard_standard_axioms CoveringDesigns.Audit17_8_6.lower_bound_explicit
#print axioms CoveringDesigns.Audit17_8_6.lower_bound_explicit
