import CoveringDesigns.Foundations.Relabelling
import Mathlib.Tactic.FinCases

/-!
Colin Barker's historical 21-block (44,11,2) witness, LJCR, 1 December 2008.
Method: simulated annealing. Labels shifted from 1–44 to 0–43; row order retained.
Daniel M. Gordon / La Jolla Covering Repository, CC BY 4.0.
Ordered original uint8 SHA-256:
523a8bdc8338e034c465532bd2207a644d8ae1131688bbcda465aa65d3a9a794.
This is a transcription and kernel verification, not a new construction.
Formalisation: Rob Gardiner, with Codex.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns.C4k_K_2.Barker

def blocks : List (Finset (Fin 44)) :=
  [
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {0, 4, 7, 11, 15, 16, 22, 23, 30, 34, 36},
    {0, 4, 7, 12, 17, 20, 24, 27, 29, 35, 42},
    {0, 7, 13, 18, 19, 26, 28, 33, 37, 39, 43},
    {0, 7, 14, 21, 25, 31, 32, 38, 40, 41, 42},
    {1, 2, 3, 12, 13, 15, 23, 26, 32, 35, 41},
    {1, 3, 11, 14, 18, 20, 21, 24, 28, 30, 31},
    {1, 3, 16, 17, 31, 33, 36, 39, 40, 42, 43},
    {1, 3, 19, 22, 25, 27, 29, 31, 34, 37, 38},
    {2, 4, 8, 13, 20, 22, 24, 26, 34, 40, 42},
    {2, 4, 8, 14, 15, 17, 19, 21, 23, 31, 37},
    {2, 8, 11, 15, 27, 29, 30, 32, 33, 41, 43},
    {2, 8, 12, 16, 18, 25, 28, 35, 36, 38, 39},
    {4, 6, 10, 15, 20, 23, 24, 25, 33, 38, 43},
    {4, 6, 10, 17, 18, 22, 28, 32, 34, 39, 41},
    {5, 9, 11, 13, 17, 25, 26, 30, 31, 38, 39},
    {5, 9, 12, 14, 21, 22, 33, 34, 35, 39, 43},
    {5, 9, 15, 18, 23, 27, 28, 29, 39, 40, 42},
    {5, 9, 16, 19, 20, 24, 32, 36, 37, 39, 41},
    {6, 10, 11, 12, 19, 30, 31, 35, 37, 40, 42},
    {6, 10, 13, 14, 16, 21, 23, 26, 27, 29, 36}
  ]

/-- Distinctness before forming the ordinary family. -/
theorem blocks_distinct : blocks.Nodup := by decide +kernel

def family : Family (Fin 44) := blocks.toFinset

theorem family_card : family.card = 21 := by decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem family_uniform : Uniform family 11 := by
  unfold Uniform family blocks
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
private theorem points_covered : ∀ a b : Fin 44,
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

theorem family_isCover : IsCover family 11 2 := ⟨family_uniform,family_covers⟩

/-- The historical ordinary family, transported to arbitrary actual point labels. -/
theorem attainment {α : Type*} [Fintype α] (hv : Fintype.card α = 44) :
    ∃ C : Family α, IsCover C 11 2 ∧ C.card = 21 := by
  classical
  let e := (Fintype.equivFinOfCardEq hv).symm
  exact ⟨relabel e family,relabel_isCover e family_isCover,
    (relabel_card e family).trans family_card⟩

end CoveringDesigns.C4k_K_2.Barker
