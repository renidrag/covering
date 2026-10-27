import CoveringDesigns.Foundations.Relabelling
import Mathlib.Tactic.FinCases

/-!
Flavio Perona's preserved 31-block (65,13,2) witness, LJCR, 2011-05-21 03:32:48.
Method recorded: (blank). Labels shifted from 1–65 to 0–64; row order retained.
Daniel M. Gordon / La Jolla Covering Repository, CC BY 4.0.
Ordered original uint8 SHA-256:
e3a90d45e3c09454e0f28b74ae9fc6d2566427d538374cc06440ce4f24d04251.
Transcription and kernel verification, not a new construction.
Formalisation: Rob Gardiner, with Codex.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns.Qk_K_2.Perona

def blocks : List (Finset (Fin 65)) :=
  [
    {0, 1, 3, 4, 7, 9, 13, 24, 25, 32, 36, 49, 62},
    {0, 2, 9, 10, 15, 16, 19, 23, 42, 44, 51, 59, 60},
    {0, 5, 8, 9, 16, 17, 20, 28, 31, 33, 46, 56, 64},
    {0, 6, 9, 11, 12, 18, 26, 30, 38, 48, 50, 54, 58},
    {0, 9, 14, 16, 29, 34, 41, 43, 45, 52, 53, 55, 63},
    {0, 9, 16, 21, 22, 27, 35, 37, 39, 40, 47, 57, 61},
    {1, 2, 13, 21, 26, 31, 33, 35, 41, 44, 45, 54, 60},
    {1, 3, 5, 8, 13, 14, 16, 19, 22, 30, 37, 43, 48},
    {1, 3, 6, 13, 23, 28, 34, 40, 47, 55, 56, 58, 59},
    {1, 3, 10, 13, 15, 18, 27, 29, 38, 39, 46, 52, 64},
    {1, 11, 12, 13, 17, 20, 42, 50, 51, 53, 57, 61, 63},
    {2, 3, 17, 19, 20, 25, 26, 27, 34, 36, 39, 54, 55},
    {2, 4, 6, 17, 20, 22, 29, 32, 37, 44, 52, 58, 60},
    {2, 5, 6, 8, 10, 15, 21, 25, 35, 36, 53, 58, 63},
    {2, 7, 10, 15, 17, 20, 24, 30, 40, 41, 45, 47, 48},
    {2, 7, 11, 12, 19, 21, 24, 28, 29, 35, 50, 52, 56},
    {2, 7, 22, 23, 24, 26, 37, 46, 53, 54, 59, 63, 64},
    {2, 14, 17, 18, 20, 21, 23, 35, 38, 43, 49, 59, 62},
    {2, 23, 25, 29, 30, 31, 33, 36, 48, 52, 57, 59, 61},
    {3, 4, 21, 30, 32, 34, 35, 42, 46, 48, 51, 55, 64},
    {3, 6, 11, 19, 41, 45, 46, 49, 57, 58, 61, 62, 64},
    {3, 10, 12, 15, 22, 31, 33, 34, 37, 49, 50, 55, 62},
    {3, 27, 28, 30, 39, 44, 48, 49, 53, 56, 60, 62, 63},
    {4, 5, 8, 11, 12, 23, 27, 32, 39, 41, 45, 50, 59},
    {4, 10, 11, 14, 15, 26, 28, 32, 43, 54, 56, 57, 61},
    {4, 11, 16, 18, 19, 31, 32, 33, 38, 40, 47, 53, 63},
    {5, 7, 8, 11, 18, 24, 34, 38, 44, 55, 57, 60, 61},
    {5, 8, 16, 26, 29, 40, 42, 47, 49, 51, 52, 54, 62},
    {6, 7, 14, 16, 24, 27, 31, 33, 39, 42, 43, 51, 58},
    {11, 18, 22, 25, 28, 36, 37, 38, 41, 42, 45, 51, 56},
    {12, 14, 16, 25, 36, 40, 43, 44, 46, 47, 50, 60, 64}
  ]

/-- Distinctness before forming the ordinary family. -/
theorem blocks_distinct : blocks.Nodup := by decide +kernel

def family : Family (Fin 65) := blocks.toFinset

theorem family_card : family.card = 31 := by decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem family_uniform : Uniform family 13 := by
  unfold Uniform family blocks
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
private theorem points_covered : ∀ a b : Fin 65,
    blocks.any (fun B => decide (a ∈ B ∧ b ∈ B)) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem family_covers : Covers family 2 := by
  intro T hT
  obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp hT
  obtain ⟨B,hB,hpoints⟩ := List.any_eq_true.mp (points_covered a b)
  have hp : a ∈ B ∧ b ∈ B := of_decide_eq_true hpoints
  exact ⟨B,List.mem_toFinset.mpr hB,
    by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using hp⟩

theorem family_isCover : IsCover family 13 2 := ⟨family_uniform,family_covers⟩

/-- The historical ordinary family, transported to arbitrary actual point labels. -/
theorem attainment {α : Type*} [Fintype α] (hv : Fintype.card α = 65) :
    ∃ C : Family α, IsCover C 13 2 ∧ C.card = 31 := by
  classical
  let e := (Fintype.equivFinOfCardEq hv).symm
  exact ⟨relabel e family,relabel_isCover e family_isCover,
    (relabel_card e family).trans family_card⟩

end CoveringDesigns.Qk_K_2.Perona
