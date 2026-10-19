import CoveringDesigns.Multicover.Schoenheim
import CoveringDesigns.HigherIncidence.Parameters

/-! Complete numerical hypotheses of Horsley–Singh Lemma 3 for positive λ. -/
namespace CoveringDesigns.MulticoverIncidence
open HigherIncidence

/-- Monotonicity of the exact nested ceilings in the initial multiplicity. -/
theorem bound_mono_multiplicity {lam₁ lam₂ : ℕ} (h : lam₁ ≤ lam₂) (v k t : ℕ) :
    Multicover.bound lam₁ v k t ≤ Multicover.bound lam₂ v k t := by
  induction t generalizing v k with
  | zero => exact h
  | succ t ih =>
    simp only [Multicover.bound_succ, Schoenheim.ceilDiv]
    exact Nat.div_le_div_right (Nat.sub_le_sub_right
      (Nat.add_le_add_right (Nat.mul_le_mul_left v (ih (v-1) (k-1))) k) 1)

structure Parameters (lam v k t s : ℕ) (b : ℕ → ℕ) : Prop where
  multiplicity_pos : 1 ≤ lam
  order_pos : 1 ≤ s
  strength : 2*s ≤ t
  strength_lt : t < k
  block_lt : k < v
  positive : ∀ i, s ≤ i → i ≤ 2*s → 0 < b i
  seed : Multicover.bound lam (v-2*s) (k-2*s) (t-2*s) ≤ b (2*s)
  step : ∀ i, s ≤ i → i < 2*s →
    Schoenheim.ceilDiv ((v-i)*b (i+1)) (k-i) ≤ b i
  coefficients : ∀ j, j ≤ s → 0 ≤ coefficient s b j

/-- Reuse the old *numerical* recurrence proofs. No conversion of coverings
or of universal smaller-cover bounds is involved. -/
theorem Parameters.toOrdinary {lam v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters lam v k t s b) : HigherIncidence.Parameters v k t s b := by
  refine ⟨h.order_pos, h.strength, h.strength_lt, h.block_lt, h.positive, ?_,
    h.step, h.coefficients⟩
  have hm := bound_mono_multiplicity h.multiplicity_pos (v-2*s) (k-2*s) (t-2*s)
  rw [Multicover.bound_one_eq] at hm
  exact hm.trans h.seed

theorem Parameters.denominator_pos {lam v k t s i : ℕ} {b : ℕ → ℕ}
    (h : Parameters lam v k t s b) (hi : i ≤ 2*s) : 0 < k-i :=
  h.toOrdinary.denominator_pos hi

theorem Parameters.recurrence {lam v k t s i : ℕ} {b : ℕ → ℕ}
    (h : Parameters lam v k t s b) (hs : s ≤ i) (hi : i < 2*s) :
    (v-i)*b (i+1) ≤ (k-i)*b i := h.toOrdinary.recurrence hs hi

theorem Parameters.binomial_recurrence {lam v k t s r : ℕ} {b : ℕ → ℕ}
    (h : Parameters lam v k t s b) (hr : r ≤ s) :
    (v-s).choose r*b (s+r) ≤ (k-s).choose r*b s :=
  h.toOrdinary.binomial_recurrence hr

theorem Parameters.defect_nonneg {lam v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters lam v k t s b) : 0 ≤ defect v k s b := h.toOrdinary.defect_nonneg

theorem Parameters.diagonal_pos {lam v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters lam v k t s b) (hd : defect v k s b < coefficient s b s) :
    0 < coefficient s b s := h.toOrdinary.diagonal_pos hd

theorem Parameters.diagonal_lt {lam v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters lam v k t s b) : coefficient s b s < (b s : ℤ) :=
  h.toOrdinary.diagonal_lt

end CoveringDesigns.MulticoverIncidence
