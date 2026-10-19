import CoveringDesigns.Foundations.Relabelling

/-!
The known twelve-block (20,11,3) covering, with labels shifted from 1–20 to 0–19.
The retained Covering Repository observation attributes this construction to
Jan de Heer, 16 May 2005. This file verifies that fixed construction; it makes
no claim of a new construction or of historical priority.

The displayed data are checked by ordinary kernel reduction. The relabelled
family uses only the public equivalence-based covering interface.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns

def knownCover12_20_11_3 : Family (Fin 20) :=
  {
    {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11},
    {0, 1, 2, 3, 4, 5, 7, 12, 13, 14, 15},
    {0, 1, 2, 3, 4, 6, 7, 16, 17, 18, 19},
    {0, 3, 5, 9, 10, 14, 15, 16, 17, 18, 19},
    {0, 3, 6, 8, 11, 12, 13, 14, 15, 16, 19},
    {0, 3, 7, 8, 9, 10, 11, 12, 13, 17, 18},
    {1, 4, 5, 8, 11, 12, 13, 16, 17, 18, 19},
    {1, 4, 6, 9, 10, 12, 13, 14, 15, 17, 18},
    {1, 4, 7, 8, 9, 10, 11, 14, 15, 16, 19},
    {2, 5, 6, 7, 8, 10, 11, 14, 15, 17, 18},
    {2, 5, 6, 7, 9, 10, 11, 12, 13, 16, 19},
    {2, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19}
  }

theorem knownCover12_20_11_3_card : knownCover12_20_11_3.card = 12 := by
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover12_20_11_3_uniform : Uniform knownCover12_20_11_3 11 := by
  unfold Uniform knownCover12_20_11_3
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover12_20_11_3_covers : Covers knownCover12_20_11_3 3 := by
  apply covers_of_powersetCard
  unfold knownCover12_20_11_3
  decide +kernel

theorem knownCover12_20_11_3_isCover : IsCover knownCover12_20_11_3 11 3 :=
  ⟨knownCover12_20_11_3_uniform, knownCover12_20_11_3_covers⟩

theorem upper_bound_20_11_3 :
    ∃ C : Family (Fin 20), IsCover C 11 3 ∧ C.card = 12 :=
  ⟨knownCover12_20_11_3, knownCover12_20_11_3_isCover, knownCover12_20_11_3_card⟩

/-- The actual historical witness transported to arbitrary twenty-point labels. -/
noncomputable def knownCover12_20_11_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover12_20_11_3

theorem knownCover12_20_11_3_on_card {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20) : (knownCover12_20_11_3_on hv).card = 12 := by
  rw [knownCover12_20_11_3_on, relabel_card, knownCover12_20_11_3_card]

theorem knownCover12_20_11_3_on_isCover {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20) : IsCover (knownCover12_20_11_3_on hv) 11 3 :=
  relabel_isCover _ knownCover12_20_11_3_isCover

theorem upper_bound_20_11_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20) :
    ∃ C : Family α, IsCover C 11 3 ∧ C.card = 12 :=
  ⟨knownCover12_20_11_3_on hv, knownCover12_20_11_3_on_isCover hv,
    knownCover12_20_11_3_on_card hv⟩

end CoveringDesigns
