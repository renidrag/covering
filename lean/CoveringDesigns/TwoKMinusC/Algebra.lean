import CoveringDesigns.MulticoverLargeDefect.LowerBound

/-! Actual-floor specialisation of Horsley–Singh's large-defect bound.
Signed arithmetic avoids truncated parameter differences.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusC
open Finset HigherIncidence LargeDefect

def seed (j : ℕ) : ℕ := if j = 1 then 6 else if j = 2 then 3 else 0

def offsetDefect (c : ℕ) : ℤ := 3 * ((c : ℤ) - 1)

noncomputable def denominator (c k : ℕ) : ℝ :=
  2*(k : ℝ)^2 + ((offsetDefect c : ℝ)-1)*k +
    (offsetDefect c : ℝ)*((offsetDefect c : ℝ)+1)

noncomputable def numerator (c k : ℕ) : ℝ :=
  (2*(k : ℝ)-c)*(14*(k : ℝ)+2*(offsetDefect c : ℝ)-12)

noncomputable def Q (c k : ℕ) : ℝ := numerator c k / denominator c k

theorem coefficient_zero : coefficient 1 seed 0 = 3 := by
  norm_num [coefficient, seed, sum_range_succ]

theorem coefficient_one : coefficient 1 seed 1 = 3 := by
  norm_num [coefficient, seed, sum_range_succ]

theorem defect_eq {v c k : ℕ} (hv : v+c=2*k) (hck : c<k) :
    defect v k 1 seed = offsetDefect c := by
  have hv1 : 1 ≤ v := by omega
  have hz : (v : ℤ)+(c : ℤ)=2*(k : ℤ) := by exact_mod_cast hv
  simp only [defect, seed, ite_eq_left, Nat.choose_one_right, sum_range_one,
    Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one]
  norm_num
  rw [Nat.cast_sub hv1]
  unfold offsetDefect
  push_cast
  omega

theorem offsetDefect_ge {c : ℕ} (hc : 2≤c) : 3 ≤ offsetDefect c := by
  unfold offsetDefect
  omega

theorem denominator_pos {c k : ℕ} (hc : 2≤c) : 0 < denominator c k := by
  have hd : (3 : ℝ) ≤ offsetDefect c := by exact_mod_cast offsetDefect_ge hc
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold denominator
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ (offsetDefect c : ℝ)-1) hk
  nlinarith [sq_nonneg (k : ℝ)]

theorem value_eq_Q {v c k : ℕ} (hv : v+c=2*k) (hc : 2≤c) (hck : c<k) :
    MulticoverLargeDefect.value v k 1 seed = Q c k := by
  have hd : (3 : ℝ) ≤ offsetDefect c := by exact_mod_cast offsetDefect_ge hc
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hvR : (v : ℝ)=2*(k : ℝ)-c := by
    have : (v : ℝ)+(c : ℝ)=2*(k : ℝ) := by exact_mod_cast hv
    linarith
  have hD := ne_of_gt (denominator_pos (k := k) hc)
  have hd1 : (offsetDefect c : ℝ)+1 ≠ 0 := by linarith
  have hdk : (offsetDefect c : ℝ)+(k : ℝ) ≠ 0 := by linarith
  simp only [MulticoverLargeDefect.value, Nat.choose_one_right, coefficient_one,
    defect_eq hv hck]
  norm_num [seed]
  unfold ratio alpha beta Q numerator
  rw [hvR]
  apply (div_eq_div_iff (by
    have h := MulticoverLargeDefect.bound_denominator_pos
      (v := v) (k := k) (s := 1) (b := seed)
      (by simpa using (show 0<k by omega))
      (by rw [coefficient_one]; norm_num)
      (by rw [defect_eq hv hck]; exact le_trans (by norm_num) (offsetDefect_ge hc))
    simpa [coefficient_one, defect_eq hv hck, alpha, beta] using ne_of_gt h) hD).mpr
  unfold denominator
  field_simp
  ring

theorem Q_nonneg {c k : ℕ} (hc : 2≤c) (hck : c<k) (hk : 6<k) :
    0 ≤ Q c k := by
  have hd : (3 : ℝ) ≤ offsetDefect c := by exact_mod_cast offsetDefect_ge hc
  have hckR : (c : ℝ)<k := by exact_mod_cast hck
  have hkR : (6 : ℝ)<k := by exact_mod_cast hk
  exact div_nonneg (mul_nonneg (by linarith) (by linarith))
    (denominator_pos hc).le

theorem Q_le_iff {c k : ℕ} {n : ℝ} (hc : 2≤c) :
    Q c k ≤ n ↔ numerator c k ≤ n * denominator c k :=
  div_le_iff₀ (denominator_pos hc)

theorem ceil_Q_le_iff {c k n : ℕ} (hc : 2≤c) :
    Nat.ceil (Q c k) ≤ n ↔ numerator c k ≤ (n : ℝ)*denominator c k :=
  Nat.ceil_le.trans (Q_le_iff hc)

end CoveringDesigns.TwoKMinusC
