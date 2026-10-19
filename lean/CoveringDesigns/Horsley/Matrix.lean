import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Unweighted positive-definiteness and incidence-rank tools for Horsley's
covering argument. The quadratic-form proof below replaces the paper's
auxiliary weighted diagonal-dominance argument.
-/

namespace CoveringDesigns.Horsley

open Finset Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- A symmetric nonnegative perturbation of a diagonal matrix is positive
definite when every row sum of the perturbation is smaller than the diagonal.
The index type may be empty. -/
theorem diagonal_add_posDef_of_row_sum_lt (ρ : ι → ℝ) (E : Matrix ι ι ℝ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hd : ∀ i, ∑ j, E i j < ρ i) :
    (Matrix.diagonal ρ + E).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply (Matrix.isHermitian_diagonal ρ).add
    simp only [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
    exact fun i j => hs j i
  · intro x hx
    have hswap : (∑ i, ∑ j, E i j * (x j)^2) =
        ∑ i, ∑ j, E i j * (x i)^2 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [hs j i]
    have hp : 0 < ∑ i, (ρ i - ∑ j, E i j) * (x i)^2 := by
      apply sum_pos'
      · intro i _
        exact mul_nonneg (sub_pos.mpr (hd i)).le (sq_nonneg _)
      · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
          simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hx
        exact ⟨i, mem_univ _, mul_pos (sub_pos.mpr (hd i)) (sq_pos_of_ne_zero hi)⟩
    have hnq : 0 ≤ ∑ i, ∑ j, E i j * (x i + x j)^2 :=
      sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hn i j) (sq_nonneg _)
    have hidentity :
        star x ⬝ᵥ ((Matrix.diagonal ρ + E) *ᵥ x) =
          (∑ i, (ρ i - ∑ j, E i j) * (x i)^2) +
            (∑ i, ∑ j, E i j * (x i + x j)^2) / 2 := by
      rw [Matrix.add_mulVec, dotProduct_add]
      simp_rw [star_trivial, dotProduct, Matrix.mulVec_diagonal]
      simp_rw [Matrix.mulVec, dotProduct, mul_sum]
      have hexpand : (∑ i, ∑ j, E i j * (x i + x j)^2) =
          (∑ i, ∑ j, E i j * (x i)^2) +
          (∑ i, ∑ j, E i j * (x j)^2) +
          2 * (∑ i, ∑ j, x i * (E i j * x j)) := by
        simp_rw [show ∀ i j, E i j * (x i + x j)^2 =
          E i j * (x i)^2 + E i j * (x j)^2 +
            2 * (x i * (E i j * x j)) by intros; ring]
        simp only [sum_add_distrib, mul_sum]
      rw [hexpand, hswap]
      simp only [sub_mul, sum_sub_distrib, sum_mul]
      have heq : (∑ i, x i * (ρ i * x i)) = ∑ i, ρ i * (x i)^2 := by
        apply sum_congr rfl
        intro i _
        ring
      rw [heq]
      ring
    rw [hidentity]
    linarith

omit [DecidableEq ι] in
/-- The all-ones matrix is positive semidefinite, including on an empty type. -/
theorem ones_posSemidef : Matrix.PosSemidef (fun (_ _ : ι) => (1 : ℝ)) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change star (1 : ℝ) = 1
    exact star_one ℝ
  · intro x
    simpa only [star_trivial, dotProduct, Matrix.mulVec, one_mul, ← sum_mul, pow_two]
      using sq_nonneg (∑ i, x i)

/-- A positive definite row Gram matrix forces at least as many columns as rows. -/
theorem card_le_of_gram_posDef [Fintype κ] (X : Matrix ι κ ℝ)
    (h : (X * X.transpose).PosDef) : Fintype.card ι ≤ Fintype.card κ := by
  rw [← Matrix.rank_of_isUnit (X * X.transpose) h.isUnit]
  exact (Matrix.rank_mul_le_left X X.transpose).trans X.rank_le_card_width

end CoveringDesigns.Horsley
