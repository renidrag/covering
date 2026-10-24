import CoveringDesigns.Foundations.Relabelling
import Mathlib.Tactic.FinCases

/-!
Historical thirteen-block (34,18,3) covering, labels shifted from 1–34 to 0–33.
Source: LJCR, “Multiple of (17,9,3) covering”, recorded 20 January 2009.
Daniel M. Gordon / La Jolla Covering Repository, CC BY 4.0.
The timestamp records witness availability, not exactness or first discovery.
Ordered source-byte SHA-256:
5f8cd4bcedf84fd8032fa2b324e073115f7baaa8729ef437149c7151d19dfa3f.
This file checks the historical construction with ordinary kernel reduction.
Formalisation: Rob Gardiner, with AI assistance.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns

def knownBlocks13_34_18_3 : List (Finset (Fin 34)) :=
  [
    {0, 1, 2, 4, 10, 11, 12, 13, 14, 17, 18, 19, 21, 27, 28, 29, 30, 31},
    {0, 1, 3, 6, 8, 10, 12, 14, 15, 17, 18, 20, 23, 25, 27, 29, 31, 32},
    {0, 1, 5, 7, 9, 10, 12, 14, 16, 17, 18, 22, 24, 26, 27, 29, 31, 33},
    {0, 2, 3, 5, 9, 10, 11, 12, 15, 17, 19, 20, 22, 26, 27, 28, 29, 32},
    {0, 2, 6, 7, 8, 10, 11, 12, 16, 17, 19, 23, 24, 25, 27, 28, 29, 33},
    {0, 3, 4, 7, 10, 12, 13, 15, 16, 17, 20, 21, 24, 27, 29, 30, 32, 33},
    {0, 4, 5, 6, 8, 9, 10, 12, 13, 17, 21, 22, 23, 25, 26, 27, 29, 30},
    {1, 2, 3, 5, 6, 7, 8, 9, 15, 18, 19, 20, 22, 23, 24, 25, 26, 32},
    {1, 2, 5, 6, 8, 9, 11, 14, 16, 18, 19, 22, 23, 25, 26, 28, 31, 33},
    {1, 3, 4, 6, 8, 11, 13, 15, 16, 18, 20, 21, 23, 25, 28, 30, 32, 33},
    {1, 4, 5, 7, 9, 11, 13, 14, 15, 18, 21, 22, 24, 26, 28, 30, 31, 32},
    {2, 3, 4, 5, 9, 13, 14, 15, 16, 19, 20, 21, 22, 26, 30, 31, 32, 33},
    {2, 3, 4, 6, 7, 8, 11, 13, 14, 19, 20, 21, 23, 24, 25, 28, 30, 31}
  ]

/-- Distinctness of the thirteen displayed blocks before forming the family. -/
theorem knownBlocks13_34_18_3_distinct : knownBlocks13_34_18_3.Nodup := by
  decide +kernel

def knownCover13_34_18_3 : Family (Fin 34) := knownBlocks13_34_18_3.toFinset

theorem knownCover13_34_18_3_card : knownCover13_34_18_3.card = 13 := by
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover13_34_18_3_uniform : Uniform knownCover13_34_18_3 18 := by
  unfold Uniform knownCover13_34_18_3 knownBlocks13_34_18_3
  decide +kernel

-- Split the finite check by its first point to bound kernel-reduction memory.
-- Repeated points are allowed here, making the final finite-set bridge direct.
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
private theorem knownCover13_34_18_3_points : ∀ a b c : Fin 34,
    knownBlocks13_34_18_3.any (fun B => decide (a ∈ B ∧ b ∈ B ∧ c ∈ B)) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem knownCover13_34_18_3_covers : Covers knownCover13_34_18_3 3 := by
  intro T hT
  obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp hT
  obtain ⟨B, hB, hpoints⟩ := List.any_eq_true.mp (knownCover13_34_18_3_points a b c)
  have hp : a ∈ B ∧ b ∈ B ∧ c ∈ B := of_decide_eq_true hpoints
  exact ⟨B, List.mem_toFinset.mpr hB,
    by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hp⟩

theorem knownCover13_34_18_3_isCover : IsCover knownCover13_34_18_3 18 3 :=
  ⟨knownCover13_34_18_3_uniform, knownCover13_34_18_3_covers⟩

theorem upper_bound_34_18_3 :
    ∃ C : Family (Fin 34), IsCover C 18 3 ∧ C.card = 13 :=
  ⟨knownCover13_34_18_3, knownCover13_34_18_3_isCover, knownCover13_34_18_3_card⟩

/-- The actual historical family transported to any thirty-four-point type. -/
noncomputable def knownCover13_34_18_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 34) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover13_34_18_3

theorem knownCover13_34_18_3_on_card {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 34) : (knownCover13_34_18_3_on hv).card = 13 := by
  rw [knownCover13_34_18_3_on, relabel_card, knownCover13_34_18_3_card]

theorem knownCover13_34_18_3_on_isCover {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 34) : IsCover (knownCover13_34_18_3_on hv) 18 3 :=
  relabel_isCover _ knownCover13_34_18_3_isCover

theorem upper_bound_34_18_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 34) :
    ∃ C : Family α, IsCover C 18 3 ∧ C.card = 13 :=
  ⟨knownCover13_34_18_3_on hv, knownCover13_34_18_3_on_isCover hv,
    knownCover13_34_18_3_on_card hv⟩

end CoveringDesigns
