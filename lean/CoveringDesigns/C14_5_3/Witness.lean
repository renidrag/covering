import CoveringDesigns.Foundations.Relabelling

/-!
Historical forty-three-block (14,5,3) covering, labels shifted from 1–14 to 0–13.
Retained source credit: “Nurmela and Östergård simulated annealing”, dated 1996-12-01.
Daniel M. Gordon / La Jolla Covering Repository, CC BY 4.0.
The timestamp is source metadata, not a verified discovery date.
Raw ordered block-byte SHA-256:
173772ab8d73847ff258f4f5ae2859d0fbe7e312483e1afc23d58c721bd22f93.
All finite claims below are checked by the ordinary Lean kernel.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns

def knownBlocks43_14_5_3 : List (Finset (Fin 14)) :=
  [
    {0, 1, 2, 4, 12},
    {0, 1, 3, 7, 11},
    {0, 1, 4, 5, 9},
    {0, 1, 4, 5, 10},
    {0, 1, 6, 8, 13},
    {0, 2, 3, 5, 8},
    {0, 2, 6, 7, 9},
    {0, 2, 10, 11, 13},
    {0, 3, 4, 6, 9},
    {0, 3, 6, 9, 10},
    {0, 3, 9, 12, 13},
    {0, 4, 5, 7, 13},
    {0, 4, 8, 9, 11},
    {0, 5, 6, 11, 12},
    {0, 7, 8, 10, 12},
    {1, 2, 3, 9, 11},
    {1, 2, 5, 7, 13},
    {1, 2, 6, 8, 10},
    {1, 3, 4, 11, 13},
    {1, 3, 5, 6, 8},
    {1, 3, 5, 8, 11},
    {1, 3, 6, 8, 11},
    {1, 3, 10, 11, 12},
    {1, 4, 6, 7, 8},
    {1, 5, 7, 12, 13},
    {1, 6, 8, 9, 12},
    {1, 7, 9, 10, 13},
    {2, 3, 4, 7, 10},
    {2, 3, 6, 7, 12},
    {2, 3, 6, 7, 13},
    {2, 4, 5, 6, 11},
    {2, 4, 8, 9, 13},
    {2, 5, 9, 10, 12},
    {2, 7, 8, 11, 13},
    {2, 8, 11, 12, 13},
    {3, 4, 5, 8, 12},
    {3, 5, 7, 8, 9},
    {3, 5, 8, 10, 13},
    {4, 6, 10, 12, 13},
    {4, 7, 9, 11, 12},
    {4, 8, 9, 10, 11},
    {5, 6, 7, 10, 11},
    {5, 6, 9, 11, 13}
  ]

/-- Distinctness of all forty-three displayed blocks, before converting to a family. -/
theorem knownBlocks43_14_5_3_distinct : knownBlocks43_14_5_3.Nodup := by
  decide +kernel

def knownCover43_14_5_3 : Family (Fin 14) := knownBlocks43_14_5_3.toFinset

theorem knownCover43_14_5_3_card : knownCover43_14_5_3.card = 43 := by
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover43_14_5_3_uniform : Uniform knownCover43_14_5_3 5 := by
  unfold Uniform knownCover43_14_5_3 knownBlocks43_14_5_3
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover43_14_5_3_covers : Covers knownCover43_14_5_3 3 := by
  apply covers_of_powersetCard
  unfold knownCover43_14_5_3 knownBlocks43_14_5_3
  decide +kernel

theorem knownCover43_14_5_3_isCover : IsCover knownCover43_14_5_3 5 3 :=
  ⟨knownCover43_14_5_3_uniform, knownCover43_14_5_3_covers⟩

theorem upper_bound_14_5_3 :
    ∃ C : Family (Fin 14), IsCover C 5 3 ∧ C.card = 43 :=
  ⟨knownCover43_14_5_3, knownCover43_14_5_3_isCover, knownCover43_14_5_3_card⟩

/-- The actual historical witness transported to arbitrary fourteen-point labels. -/
noncomputable def knownCover43_14_5_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 14) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover43_14_5_3

theorem knownCover43_14_5_3_on_card {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 14) : (knownCover43_14_5_3_on hv).card = 43 := by
  rw [knownCover43_14_5_3_on, relabel_card, knownCover43_14_5_3_card]

theorem knownCover43_14_5_3_on_isCover {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 14) : IsCover (knownCover43_14_5_3_on hv) 5 3 :=
  relabel_isCover _ knownCover43_14_5_3_isCover

theorem upper_bound_14_5_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 14) :
    ∃ C : Family α, IsCover C 5 3 ∧ C.card = 43 :=
  ⟨knownCover43_14_5_3_on hv, knownCover43_14_5_3_on_isCover hv,
    knownCover43_14_5_3_on_card hv⟩

end CoveringDesigns
