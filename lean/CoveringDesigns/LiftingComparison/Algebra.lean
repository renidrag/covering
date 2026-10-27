import CoveringDesigns.LargeDefect.Algebra

/-! The algebra behind Horsley–Singh Remark 14. No covering or rank hypotheses.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.LiftingComparison
open LargeDefect

/-- Clearing denominators; neither coefficient order nor positivity is needed. -/
theorem difference_identity (N K m : ℕ) {A B : ℝ}
    (hK : K ≠ 0) (hD : (K : ℝ)*(A-B)+1 ≠ 0) :
    (N : ℝ)*(m+1)/K - ratio N K m A B =
      (N : ℝ)*(m+1-(K : ℝ)*B)/((K : ℝ)*((K : ℝ)*(A-B)+1)) := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  unfold ratio
  field_simp
  ring

/-- The weak threshold suffices, including N=0. -/
theorem ratio_le_of_threshold {N K m : ℕ} {A B : ℝ}
    (hK : 0 < K) (hD : 0 < (K : ℝ)*(A-B)+1)
    (hB : (K : ℝ)*B ≤ m+1) : ratio N K m A B ≤ (N : ℝ)*(m+1)/K := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have he := difference_identity N K m (Nat.ne_of_gt hK) (ne_of_gt hD)
  have hn := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (sub_nonneg.mpr hB)
  have := div_nonneg hn (mul_pos hk hD).le
  linarith

theorem ratio_le_iff_threshold {N K m : ℕ} {A B : ℝ}
    (hN : 0 < N) (hK : 0 < K) (hD : 0 < (K : ℝ)*(A-B)+1) :
    ratio N K m A B ≤ (N : ℝ)*(m+1)/K ↔ (K : ℝ)*B ≤ m+1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  rw [← sub_nonneg, difference_identity N K m (Nat.ne_of_gt hK) (ne_of_gt hD)]
  rw [le_div_iff₀ (mul_pos hk hD)]
  simp only [zero_mul, mul_nonneg_iff_of_pos_left hn, sub_nonneg]

theorem ratio_lt_iff_threshold {N K m : ℕ} {A B : ℝ}
    (hN : 0 < N) (hK : 0 < K) (hD : 0 < (K : ℝ)*(A-B)+1) :
    ratio N K m A B < (N : ℝ)*(m+1)/K ↔ (K : ℝ)*B < m+1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  rw [← sub_pos, difference_identity N K m (Nat.ne_of_gt hK) (ne_of_gt hD)]
  rw [lt_div_iff₀ (mul_pos hk hD)]
  simp only [zero_mul, mul_pos_iff_of_pos_left hn, sub_pos]

theorem ratio_eq_iff_threshold {N K m : ℕ} {A B : ℝ}
    (hN : 0 < N) (hK : 0 < K) (hD : 0 < (K : ℝ)*(A-B)+1) :
    ratio N K m A B = (N : ℝ)*(m+1)/K ↔ (K : ℝ)*B = m+1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [eq_comm (a := ratio N K m A B), ← sub_eq_zero,
    difference_identity N K m (Nat.ne_of_gt hK) (ne_of_gt hD)]
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  simp only [div_eq_zero_iff, mul_eq_zero, hn, hk, ne_of_gt hD, false_or, or_false,
    sub_eq_zero]
  exact eq_comm

@[simp] theorem ratio_zero (K m : ℕ) (A B : ℝ) : ratio 0 K m A B = 0 := by
  simp [ratio]

/-- The source's strict coefficient chain, with no upper bound on d. -/
theorem theorem15_beta_chain {K m : ℕ} {a d : ℝ}
    (hK : 0 < K) (ha : 0 ≤ a) (hd : 0 < d) (ham : a < m) :
    (K : ℝ)*beta K a d < (a+1)/2 ∧ (a+1)/2 < a+1 ∧ a+1 < (m : ℝ)+1 := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hp : 0 < 2*(d+(K : ℝ)) := by positivity
  refine ⟨?_, by linarith, by linarith⟩
  rw [beta, ← mul_div_assoc, div_lt_iff₀ hp]
  nlinarith [mul_pos hd (show 0 < a+1 by linarith)]

end CoveringDesigns.LiftingComparison
