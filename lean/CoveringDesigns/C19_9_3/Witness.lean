import CoveringDesigns.Foundations.Relabelling
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Tactic.FinCases

/-!
Rade Belic's historical seventeen-block (19,9,3) covering.
LJCR records the construction on 11 June 1997. Data: CC BY 4.0;
Daniel M. Gordon / La Jolla Covering Repository, Zenodo 19735294, v1.2.
Point labels are shifted from 1–19 to 0–18, preserving row and point order.
Ordered source-byte SHA-256:
53bd57d226f1d42fb579bbb4538e888d78ef6f55afe93c150b8c726e70ae2841.
The external checker verifies transcription; Lean proves this literal's
covering properties by ordinary kernel reduction. No optimality is asserted
by this witness module. Formalisation: Rob Gardiner, with AI assistance.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns

def knownBlocks17_19_9_3 : List (Finset (Fin 19)) :=
  [
    {0, 1, 2, 3, 4, 5, 10, 11, 18},
    {0, 1, 2, 3, 10, 11, 12, 17, 18},
    {0, 1, 3, 4, 5, 10, 11, 12, 17},
    {0, 1, 3, 6, 7, 11, 12, 13, 15},
    {0, 1, 3, 8, 9, 11, 12, 14, 16},
    {0, 2, 3, 5, 6, 9, 14, 15, 17},
    {0, 2, 3, 5, 7, 8, 13, 16, 17},
    {0, 3, 4, 6, 8, 10, 15, 16, 18},
    {0, 3, 4, 7, 9, 10, 13, 14, 18},
    {1, 2, 4, 5, 6, 8, 11, 13, 14},
    {1, 2, 4, 5, 7, 9, 11, 15, 16},
    {1, 6, 9, 10, 11, 13, 16, 17, 18},
    {1, 7, 8, 10, 11, 14, 15, 17, 18},
    {2, 4, 6, 7, 8, 9, 12, 16, 17},
    {2, 5, 6, 7, 10, 12, 14, 16, 18},
    {2, 5, 8, 9, 10, 12, 13, 15, 18},
    {4, 5, 12, 13, 14, 15, 16, 17, 18}
  ]

/-- Distinctness of the seventeen displayed blocks before forming the family. -/
theorem knownBlocks17_19_9_3_distinct : knownBlocks17_19_9_3.Nodup := by
  decide +kernel

theorem knownBlocks17_19_9_3_length : knownBlocks17_19_9_3.length = 17 := by
  decide +kernel

def knownCover17_19_9_3 : Family (Fin 19) := knownBlocks17_19_9_3.toFinset

/-- Explicit membership correspondence between the literal ordered list
and the ordinary family verified below. -/
theorem knownCover17_19_9_3_mem (B : Finset (Fin 19)) :
    B ∈ knownCover17_19_9_3 ↔ B ∈ knownBlocks17_19_9_3 := by
  exact List.mem_toFinset

theorem triple_count_19_9_3 : ((Finset.univ : Finset (Fin 19)).powersetCard 3).card = 969 := by
  rw [Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
  decide +kernel

theorem knownCover17_19_9_3_card : knownCover17_19_9_3.card = 17 := by
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover17_19_9_3_uniform : Uniform knownCover17_19_9_3 9 := by
  unfold Uniform knownCover17_19_9_3 knownBlocks17_19_9_3
  decide +kernel

-- Split the finite check by its first point to bound kernel-reduction memory.
-- Repeated points are allowed here, making the final finite-set bridge direct.
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
private theorem knownCover17_19_9_3_points : ∀ a b c : Fin 19,
    knownBlocks17_19_9_3.any (fun B => decide (a ∈ B ∧ b ∈ B ∧ c ∈ B)) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem knownCover17_19_9_3_covers : Covers knownCover17_19_9_3 3 := by
  intro T hT
  obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp hT
  obtain ⟨B, hB, hpoints⟩ := List.any_eq_true.mp (knownCover17_19_9_3_points a b c)
  have hp : a ∈ B ∧ b ∈ B ∧ c ∈ B := of_decide_eq_true hpoints
  exact ⟨B, List.mem_toFinset.mpr hB,
    by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hp⟩

theorem knownCover17_19_9_3_isCover : IsCover knownCover17_19_9_3 9 3 :=
  ⟨knownCover17_19_9_3_uniform, knownCover17_19_9_3_covers⟩

theorem upper_bound_19_9_3 :
    ∃ C : Family (Fin 19), IsCover C 9 3 ∧ C.card = 17 :=
  ⟨knownCover17_19_9_3, knownCover17_19_9_3_isCover, knownCover17_19_9_3_card⟩

/-- The actual historical family transported to any nineteen-point type. -/
noncomputable def knownCover17_19_9_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 19) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover17_19_9_3

theorem knownCover17_19_9_3_on_card {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 19) : (knownCover17_19_9_3_on hv).card = 17 := by
  rw [knownCover17_19_9_3_on, relabel_card, knownCover17_19_9_3_card]

theorem knownCover17_19_9_3_on_isCover {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 19) : IsCover (knownCover17_19_9_3_on hv) 9 3 :=
  relabel_isCover _ knownCover17_19_9_3_isCover

theorem upper_bound_19_9_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 19) :
    ∃ C : Family α, IsCover C 9 3 ∧ C.card = 17 :=
  ⟨knownCover17_19_9_3_on hv, knownCover17_19_9_3_on_isCover hv,
    knownCover17_19_9_3_on_card hv⟩

end CoveringDesigns
