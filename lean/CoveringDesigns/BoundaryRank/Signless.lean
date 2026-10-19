import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A signless form at the diagonal-dominance boundary

Standard weighted signless-form reasoning, formalised by Rob Gardiner with AI
assistance.  The identities retain arbitrary real nonnegative edge weights and
nonnegative deficits.  No strict diagonal-dominance assertion is made.
-/

namespace CoveringDesigns.BoundaryRank

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact weighted sum-of-squares identity.  The diagonal values may vary;
zero diagonal for `E` is only needed later, for the component-size bound. -/
theorem signless_sum_squares (ρ δ : ι → ℝ) (E : Matrix ι ι ℝ)
    (hs : ∀ i j, E i j = E j i)
    (hrow : ∀ i, (∑ j, E i j) + δ i = ρ i) (x : ι → ℝ) :
    star x ⬝ᵥ ((Matrix.diagonal ρ + E) *ᵥ x) =
      (∑ i, δ i * (x i)^2) +
        (∑ i, ∑ j, E i j * (x i + x j)^2) / 2 := by
  have hswap : (∑ i, ∑ j, E i j * (x j)^2) =
      ∑ i, ∑ j, E i j * (x i)^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hs j i]
  have hexpand : (∑ i, ∑ j, E i j * (x i + x j)^2) =
      (∑ i, ∑ j, E i j * (x i)^2) +
      (∑ i, ∑ j, E i j * (x j)^2) +
      2 * (∑ i, ∑ j, x i * (E i j * x j)) := by
    simp_rw [show ∀ i j, E i j * (x i + x j)^2 =
      E i j * (x i)^2 + E i j * (x j)^2 +
        2 * (x i * (E i j * x j)) by intros; ring]
    simp only [sum_add_distrib, mul_sum]
  rw [Matrix.add_mulVec, dotProduct_add]
  simp_rw [star_trivial, dotProduct, Matrix.mulVec_diagonal]
  simp_rw [Matrix.mulVec, dotProduct, mul_sum]
  rw [hexpand, hswap]
  have heq : (∑ i, x i * (ρ i * x i)) =
      (∑ i, δ i * (x i)^2) + (∑ i, ∑ j, E i j * (x i)^2) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [← sum_mul, ← hrow i]
    ring
  rw [heq]
  ring

/-- Weak diagonal dominance with nonnegative deficits gives semidefiniteness. -/
theorem signless_posSemidef (ρ δ : ι → ℝ) (E : Matrix ι ι ℝ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ i) :
    (Matrix.diagonal ρ + E).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply (Matrix.isHermitian_diagonal ρ).add
    simp only [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
    exact fun i j => hs j i
  · intro x
    rw [signless_sum_squares ρ δ E hs hrow x]
    exact add_nonneg
      (sum_nonneg fun i _ => mul_nonneg (hδ i) (sq_nonneg _))
      (div_nonneg
        (sum_nonneg fun i _ => sum_nonneg fun j _ =>
          mul_nonneg (hn i j) (sq_nonneg _)) (by norm_num))

/-- A zero quadratic form forces every positive-deficit coordinate to vanish
and every positive-weight edge to have opposite endpoint coordinates. -/
theorem kernel_restrictions (ρ δ : ι → ℝ) (E : Matrix ι ι ℝ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ i)
    {x : ι → ℝ} (hx : (Matrix.diagonal ρ + E) *ᵥ x = 0) :
    (∀ i, 0 < δ i → x i = 0) ∧ (∀ i j, 0 < E i j → x i + x j = 0) := by
  have hq : star x ⬝ᵥ ((Matrix.diagonal ρ + E) *ᵥ x) = 0 := by simp [hx]
  rw [signless_sum_squares ρ δ E hs hrow x] at hq
  have hd : 0 ≤ ∑ i, δ i * (x i)^2 :=
    sum_nonneg fun i _ => mul_nonneg (hδ i) (sq_nonneg _)
  have he : 0 ≤ ∑ i, ∑ j, E i j * (x i + x j)^2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hn i j) (sq_nonneg _)
  have hd0 : (∑ i, δ i * (x i)^2) = 0 := by linarith
  have he0 : (∑ i, ∑ j, E i j * (x i + x j)^2) = 0 := by linarith
  constructor
  · intro i hi
    have hz : δ i * (x i)^2 = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hδ i) (sq_nonneg _))).mp hd0 i
        (mem_univ _)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hi))
  · intro i j hij
    have hrow0 : (∑ j, E i j * (x i + x j)^2) = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun i _ =>
        sum_nonneg fun j _ => mul_nonneg (hn i j) (sq_nonneg _))).mp he0 i (mem_univ _)
    have hz : E i j * (x i + x j)^2 = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun j _ =>
        mul_nonneg (hn i j) (sq_nonneg _))).mp hrow0 j (mem_univ _)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hij))

/-- The local restrictions are also sufficient for membership in the kernel. -/
theorem kernel_of_restrictions (ρ δ : ι → ℝ) (E : Matrix ι ι ℝ)
    (hn : ∀ i j, 0 ≤ E i j) (hδ : ∀ i, 0 ≤ δ i)
    (hrow : ∀ i, (∑ j, E i j) + δ i = ρ i)
    {x : ι → ℝ} (hd : ∀ i, 0 < δ i → x i = 0)
    (he : ∀ i j, 0 < E i j → x i + x j = 0) :
    (Matrix.diagonal ρ + E) *ᵥ x = 0 := by
  rw [Matrix.add_mulVec]
  apply funext
  intro i
  simp only [Pi.add_apply, Matrix.mulVec_diagonal, Pi.zero_apply]
  have hdef : δ i * x i = 0 := by
    by_cases hi : δ i = 0
    · simp [hi]
    · rw [hd i (lt_of_le_of_ne (hδ i) (Ne.symm hi)), mul_zero]
  have hedge : ∀ j, E i j * (x i + x j) = 0 := by
    intro j
    by_cases hij : E i j = 0
    · simp [hij]
    · rw [he i j (lt_of_le_of_ne (hn i j) (Ne.symm hij)), mul_zero]
  have hsum : (∑ j, E i j) * x i + ∑ j, E i j * x j = 0 := by
    rw [sum_mul, ← sum_add_distrib]
    simpa only [mul_add] using sum_eq_zero (fun j _ => hedge j)
  change ρ i * x i + (∑ j, E i j * x j) = 0
  rw [← hrow i]
  nlinarith

omit [DecidableEq ι] in
/-- Positive-semidefinite addition can only shrink the kernel.  The proof
explicitly uses nonnegativity of both quadratic forms and their zero-form
characterisation; it is not an assertion about arbitrary matrix addition. -/
theorem ker_add_le_of_posSemidef {A P : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hP : P.PosSemidef) :
    LinearMap.ker (A + P).mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  intro x hx
  change (A + P) *ᵥ x = 0 at hx
  change A *ᵥ x = 0
  apply hA.dotProduct_mulVec_zero_iff.mp
  have hq : star x ⬝ᵥ ((A + P) *ᵥ x) = 0 := by simp [hx]
  rw [Matrix.add_mulVec, dotProduct_add] at hq
  have ha := hA.dotProduct_mulVec_nonneg x
  have hp := hP.dotProduct_mulVec_nonneg x
  linarith

end CoveringDesigns.BoundaryRank
