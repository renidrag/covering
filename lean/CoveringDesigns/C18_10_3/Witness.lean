import CoveringDesigns.Foundations.Relabelling

/-!
Historical twelve-block (18,10,3) covering, labels shifted from 1–18 to 0–17.
Retained source credit: “JCD article”, timestamp 1996-11-14 17:08:00.
Daniel M. Gordon / La Jolla Covering Repository, CC BY 4.0.
The timestamp is source metadata, not a verified discovery date.
Raw ordered block-byte SHA-256:
173e0a39baa3814f25da9156a861600b0a791ff4437708d55049c85698b3d28a.
All finite claims below are checked by the ordinary Lean kernel.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns

def knownBlocks12_18_10_3 : List (Finset (Fin 18)) :=
  [
    {0, 1, 2, 3, 4, 9, 10, 11, 12, 13},
    {0, 1, 3, 5, 8, 9, 10, 12, 14, 17},
    {0, 1, 5, 6, 7, 9, 10, 14, 15, 16},
    {0, 2, 4, 5, 6, 9, 11, 13, 14, 15},
    {0, 2, 4, 7, 8, 9, 11, 13, 16, 17},
    {0, 3, 6, 7, 8, 9, 12, 15, 16, 17},
    {1, 2, 3, 6, 7, 10, 11, 12, 15, 16},
    {1, 2, 5, 7, 8, 10, 11, 14, 16, 17},
    {1, 3, 4, 5, 7, 10, 12, 13, 14, 16},
    {1, 3, 4, 6, 8, 10, 12, 13, 15, 17},
    {2, 3, 5, 6, 8, 11, 12, 14, 15, 17},
    {4, 5, 6, 7, 8, 13, 14, 15, 16, 17}
  ]

/-- Distinctness of all twelve displayed blocks, before converting to a family. -/
theorem knownBlocks12_18_10_3_distinct : knownBlocks12_18_10_3.Nodup := by
  decide +kernel

def knownCover12_18_10_3 : Family (Fin 18) := knownBlocks12_18_10_3.toFinset

theorem knownCover12_18_10_3_card : knownCover12_18_10_3.card = 12 := by
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover12_18_10_3_uniform : Uniform knownCover12_18_10_3 10 := by
  unfold Uniform knownCover12_18_10_3 knownBlocks12_18_10_3
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover12_18_10_3_covers : Covers knownCover12_18_10_3 3 := by
  apply covers_of_powersetCard
  unfold knownCover12_18_10_3 knownBlocks12_18_10_3
  decide +kernel

theorem knownCover12_18_10_3_isCover : IsCover knownCover12_18_10_3 10 3 :=
  ⟨knownCover12_18_10_3_uniform, knownCover12_18_10_3_covers⟩

theorem upper_bound_18_10_3 :
    ∃ C : Family (Fin 18), IsCover C 10 3 ∧ C.card = 12 :=
  ⟨knownCover12_18_10_3, knownCover12_18_10_3_isCover, knownCover12_18_10_3_card⟩

/-- The actual historical witness transported to arbitrary eighteen-point labels. -/
noncomputable def knownCover12_18_10_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 18) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover12_18_10_3

theorem knownCover12_18_10_3_on_card {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 18) : (knownCover12_18_10_3_on hv).card = 12 := by
  rw [knownCover12_18_10_3_on, relabel_card, knownCover12_18_10_3_card]

theorem knownCover12_18_10_3_on_isCover {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 18) : IsCover (knownCover12_18_10_3_on hv) 10 3 :=
  relabel_isCover _ knownCover12_18_10_3_isCover

theorem upper_bound_18_10_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 18) :
    ∃ C : Family α, IsCover C 10 3 ∧ C.card = 12 :=
  ⟨knownCover12_18_10_3_on hv, knownCover12_18_10_3_on_isCover hv,
    knownCover12_18_10_3_on_card hv⟩

end CoveringDesigns
