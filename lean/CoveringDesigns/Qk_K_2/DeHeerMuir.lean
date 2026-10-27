import CoveringDesigns.Foundations.Relabelling
import Mathlib.Tactic.FinCases

/-!
Jan de Heer and Steve Muir's preserved 31-block (95,19,2) witness, LJCR, 2011-03-16 12:50:04.
Method recorded: Private tools. Labels shifted from 1–95 to 0–94; row order retained.
Daniel M. Gordon / La Jolla Covering Repository, CC BY 4.0.
Ordered original uint8 SHA-256:
737d45c06ddb51ff1062b9c5ee0ce4bda1f485ac9f8fe68656b5958145ad9cb3.
Transcription and kernel verification, not a new construction.
Formalisation: Rob Gardiner, with Codex.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns.Qk_K_2.DeHeerMuir

def blocks : List (Finset (Fin 95)) :=
  [
    {0, 1, 2, 3, 4, 5, 31, 32, 34, 35, 36, 62, 63, 64, 65, 66, 67, 93, 94},
    {0, 2, 6, 12, 18, 24, 30, 33, 37, 43, 49, 55, 61, 64, 68, 74, 80, 86, 92},
    {0, 3, 8, 15, 17, 24, 26, 34, 39, 46, 48, 55, 57, 65, 70, 77, 79, 86, 88},
    {0, 6, 7, 8, 9, 10, 31, 37, 38, 39, 40, 41, 62, 68, 69, 70, 71, 72, 94},
    {0, 11, 12, 13, 14, 15, 31, 42, 43, 44, 45, 46, 62, 73, 74, 75, 76, 77, 94},
    {0, 16, 17, 18, 19, 20, 31, 47, 48, 49, 50, 51, 62, 78, 79, 80, 81, 82, 94},
    {0, 21, 22, 23, 24, 25, 31, 52, 53, 54, 55, 56, 62, 83, 84, 85, 86, 87, 94},
    {0, 26, 27, 28, 29, 30, 31, 57, 58, 59, 60, 61, 62, 88, 89, 90, 91, 92, 94},
    {1, 3, 7, 12, 17, 22, 27, 32, 38, 43, 48, 53, 58, 63, 69, 74, 79, 84, 89},
    {1, 6, 11, 16, 21, 26, 32, 37, 42, 47, 52, 57, 63, 68, 73, 78, 83, 88, 90},
    {1, 8, 13, 18, 23, 28, 32, 39, 44, 49, 54, 59, 63, 70, 75, 80, 84, 85, 90},
    {1, 9, 14, 19, 24, 29, 32, 40, 45, 50, 55, 60, 63, 71, 76, 81, 86, 91, 93},
    {1, 10, 15, 20, 25, 30, 32, 33, 41, 46, 51, 56, 61, 63, 72, 77, 82, 87, 92},
    {2, 7, 13, 19, 25, 26, 33, 38, 44, 50, 56, 57, 64, 69, 75, 81, 87, 88, 94},
    {2, 8, 14, 20, 21, 27, 33, 39, 45, 51, 52, 58, 64, 70, 76, 82, 83, 89, 93},
    {2, 9, 15, 16, 22, 28, 31, 33, 40, 46, 47, 53, 59, 64, 71, 77, 78, 84, 90},
    {2, 10, 11, 17, 23, 29, 33, 41, 42, 48, 54, 60, 62, 64, 72, 73, 79, 85, 91},
    {3, 6, 13, 20, 22, 29, 33, 34, 37, 44, 51, 53, 60, 65, 68, 75, 82, 84, 91},
    {3, 7, 14, 16, 23, 30, 34, 38, 45, 47, 54, 61, 65, 69, 76, 78, 85, 92, 93},
    {3, 9, 11, 18, 25, 27, 34, 40, 42, 49, 56, 58, 65, 71, 73, 80, 87, 89, 93},
    {3, 10, 12, 19, 21, 28, 34, 41, 43, 50, 52, 59, 65, 66, 72, 74, 81, 83, 90},
    {4, 6, 14, 17, 25, 28, 35, 37, 45, 48, 56, 59, 66, 68, 76, 79, 87, 90, 93},
    {4, 7, 15, 18, 21, 29, 35, 38, 46, 49, 52, 60, 66, 69, 77, 80, 83, 91, 93},
    {4, 8, 11, 13, 19, 22, 30, 35, 39, 42, 50, 53, 61, 66, 70, 73, 81, 84, 92},
    {4, 9, 12, 20, 23, 26, 33, 35, 40, 43, 51, 54, 57, 66, 71, 74, 82, 85, 88},
    {4, 10, 13, 16, 24, 27, 35, 41, 44, 47, 55, 58, 66, 72, 75, 78, 86, 89, 93},
    {5, 6, 15, 19, 23, 27, 36, 37, 46, 50, 54, 58, 67, 68, 77, 80, 81, 85, 89},
    {5, 7, 11, 20, 24, 28, 33, 36, 38, 42, 51, 55, 59, 67, 69, 73, 82, 86, 90},
    {5, 8, 12, 16, 25, 29, 36, 39, 43, 47, 56, 60, 67, 70, 74, 78, 87, 91, 93},
    {5, 9, 13, 17, 21, 30, 36, 40, 44, 48, 52, 61, 67, 71, 75, 79, 83, 88, 92},
    {5, 10, 14, 18, 22, 26, 36, 41, 45, 49, 53, 57, 67, 72, 76, 80, 84, 88, 93}
  ]

/-- Distinctness before forming the ordinary family. -/
theorem blocks_distinct : blocks.Nodup := by decide +kernel

def family : Family (Fin 95) := blocks.toFinset

theorem family_card : family.card = 31 := by decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem family_uniform : Uniform family 19 := by
  unfold Uniform family blocks
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
private theorem points_covered : ∀ a b : Fin 95,
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

theorem family_isCover : IsCover family 19 2 := ⟨family_uniform,family_covers⟩

/-- The historical ordinary family, transported to arbitrary actual point labels. -/
theorem attainment {α : Type*} [Fintype α] (hv : Fintype.card α = 95) :
    ∃ C : Family α, IsCover C 19 2 ∧ C.card = 31 := by
  classical
  let e := (Fintype.equivFinOfCardEq hv).symm
  exact ⟨relabel e family,relabel_isCover e family_isCover,
    (relabel_card e family).trans family_card⟩

end CoveringDesigns.Qk_K_2.DeHeerMuir
