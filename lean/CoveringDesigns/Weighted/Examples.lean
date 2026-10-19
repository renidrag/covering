import CoveringDesigns.Weighted.Pairs
import CoveringDesigns.Weighted.Counting
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! Boundary and integration checks for general weighted foundations. -/
namespace CoveringDesigns.Weighted.Examples
open Finset Matrix

theorem unit_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℝ) (E : Matrix ι ι ℝ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hd : ∀ i, ∑ j, E i j < ρ i) :
    (Matrix.diagonal ρ + E).PosDef := by
  apply diagonal_add_posDef_of_weighted_row_sum_lt ρ (fun _ => 1) E hs hn
  · intro i; norm_num
  · simpa using hd

/-- The first unweighted row fails, but positive weights (7,3) give 6<7 and 14<15. -/
theorem weighted_two_by_two :
    (Matrix.diagonal ![(1 : ℝ), 5] + !![0, 2; 2, 0]).PosDef ∧
      ¬ (∑ j : Fin 2, (!![0, 2; 2, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 j) < 1 := by
  constructor
  · apply diagonal_add_posDef_of_weighted_row_sum_lt ![1, 5] ![7, 3] !![0, 2; 2, 0]
    · intro i j; fin_cases i <;> fin_cases j <;> norm_num
    · intro i j; fin_cases i <;> fin_cases j <;> norm_num
    · intro i; fin_cases i <;> norm_num
    · intro i; fin_cases i <;> norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]

theorem zero_excess {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) :
    (Matrix.diagonal ρ + (0 : Matrix ι ι ℝ)).PosDef := by
  apply diagonal_add_posDef_of_weighted_row_sum_lt ρ (fun _ => 1) 0
  · intros; rfl
  · intros; exact le_rfl
  · intros; norm_num
  · simpa using hρ

/-- On the empty index type even positivity of the weights is vacuous. -/
theorem empty_matrix :
    (Matrix.diagonal (fun _ : Fin 0 => (0 : ℝ)) + 0).PosDef := by
  apply diagonal_add_posDef_of_weighted_row_sum_lt _ (fun _ => 0) 0
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

theorem empty_selected_pairs {α : Type*} [Fintype α] [DecidableEq α]
    (C : Family α) : (∅ : Finset (Finset α)).card ≤ C.card := by
  apply selected_pairs_card_le (b₂ := 0) (b₃ := 0) (b₄ := 0)
    (by rfl) (by intros; exact Nat.zero_le _) (by intros; exact Nat.zero_le _)
    ∅ (by simp) (fun _ => 1)
  · intro X; norm_num
  · intro X
    exact False.elim (Finset.notMem_empty X.val X.property)

theorem beta_zero {ι : Type*} (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : α * (S.filter (fun x => u x = m)).card ≤ b) :
    (S.card : ℝ)*((m : ℝ)*α+α) ≤ (b : ℝ)*((K : ℝ)*α+1) := by
  simpa using two_level_bound S u (β := 0) (by rfl) (by simpa using hα) hl hs
    (by simpa using hr)

theorem alpha_eq_two_beta {ι : Type*} (S : Finset ι) (u : ι → ℕ)
    {m K b : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : (2*β) * (S.filter (fun x => u x = m)).card +
      β * (S.filter (fun x => u x = m+1)).card ≤ b) :
    (S.card : ℝ)*((m : ℝ)*β+2*β) ≤ (b : ℝ)*((K : ℝ)*β+1) := by
  have h := two_level_bound S u hβ (le_refl (2*β)) hl hs hr
  rwa [show 2*β-β=β by ring] at h

theorem empty_counting {ι : Type*} (u : ι → ℕ) (m K : ℕ) {α β : ℝ}
    (hβ : 0 ≤ β) (hα : 2*β ≤ α) :
    ⌈((∅ : Finset ι).card : ℝ)*((m : ℝ)*(α-β)+α) / ((K : ℝ)*(α-β)+1)⌉₊ ≤ 0 :=
  two_level_ceiling ∅ u hβ hα (by simp) (by simp) (by simp)

end CoveringDesigns.Weighted.Examples
