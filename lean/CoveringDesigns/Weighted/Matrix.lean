import CoveringDesigns.Horsley.Matrix
import Mathlib.Algebra.Order.Star.Real

/-! Weighted matrix and Gram-rank foundations for Horsley–Singh Lemma 16.
Symmetric congruence replaces column scaling. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.Weighted
open Finset Matrix
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Weighted strict dominance implies positive definiteness. No nonemptiness
or zero-diagonal assumption is needed for this sufficient condition. -/
theorem diagonal_add_posDef_of_weighted_row_sum_lt (ρ c : ι → ℝ)
    (E : Matrix ι ι ℝ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hc : ∀ i, 0 < c i)
    (hd : ∀ i, ∑ j, E i j * c j < ρ i * c i) :
    (Matrix.diagonal ρ + E).PosDef := by
  have hp : (Matrix.diagonal (fun i => c i * (ρ i * c i)) +
      Matrix.of (fun i j => c i * E i j * c j)).PosDef := by
    apply Horsley.diagonal_add_posDef_of_row_sum_lt
    · intro i j
      change c i * E i j * c j = c j * E j i * c i
      rw [hs i j]
      ring
    · intro i j
      exact mul_nonneg (mul_nonneg (hc i).le (hn i j)) (hc j).le
    · intro i
      simpa only [Matrix.of_apply, mul_sum, mul_assoc] using
        mul_lt_mul_of_pos_left (hd i) (hc i)
  have he : star (Matrix.diagonal c) * (Matrix.diagonal ρ + E) * Matrix.diagonal c =
      Matrix.diagonal (fun i => c i * (ρ i * c i)) +
        Matrix.of (fun i j => c i * E i j * c j) := by
    ext i j
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      star_trivial, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
      Matrix.of_apply]
    by_cases h : i = j
    · subst j
      simp
      ring
    · simp [Matrix.diagonal_apply_ne _ h]
  have hu : IsUnit (Matrix.diagonal c) := (Matrix.PosDef.diagonal hc).isUnit
  exact hu.posDef_star_left_conjugate_iff.mp (he.symm ▸ hp)

/-- A positive-semidefinite remainder may be added before the Gram-rank bound.
The row and column types can both be empty. -/
theorem gram_card_le_of_weighted_row_sum_lt [Fintype κ]
    (X : Matrix ι κ ℝ) (ρ c : ι → ℝ) (E P : Matrix ι ι ℝ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hc : ∀ i, 0 < c i) (hd : ∀ i, ∑ j, E i j * c j < ρ i * c i)
    (hP : P.PosSemidef)
    (hgram : X * X.transpose = Matrix.diagonal ρ + E + P) :
    Fintype.card ι ≤ Fintype.card κ := by
  apply Horsley.card_le_of_gram_posDef X
  rw [hgram]
  exact (diagonal_add_posDef_of_weighted_row_sum_lt ρ c E hs hn hc hd).add_posSemidef hP

end CoveringDesigns.Weighted
