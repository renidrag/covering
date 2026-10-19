import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact coefficient algebra for Horsley–Singh Theorem 15.
This module is independent of incidence and covering theory.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.LargeDefect

noncomputable def alpha (a d : ℝ) : ℝ := (a+1)/(2*(d+1))
noncomputable def beta (K : ℕ) (a d : ℝ) : ℝ := (a+1)/(2*(d+K))

noncomputable def ratio (N K m : ℕ) (A B : ℝ) : ℝ :=
  N*((m : ℝ)*(A-B)+A)/((K : ℝ)*(A-B)+1)

theorem alpha_pos {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) : 0 < alpha a d := by
  unfold alpha
  positivity

theorem beta_pos {K : ℕ} {a d : ℝ} (hK : 0 < K) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    0 < beta K a d := by
  have : (0 : ℝ) < K := by exact_mod_cast hK
  unfold beta
  positivity

theorem beta_le_alpha {K : ℕ} {a d : ℝ} (hK : 0 < K) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    beta K a d ≤ alpha a d := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hd1 : 0 < 2*(d+1) := by positivity
  have hdk : 0 < 2*(d+(K : ℝ)) := by linarith
  rw [beta, alpha, div_le_div_iff₀ hdk hd1]
  nlinarith

/-- This weaker coefficient order suffices for every denominator in Theorem 15. -/
theorem ratio_denominator_pos (K : ℕ) {A B : ℝ} (hAB : B ≤ A) :
    0 < (K : ℝ)*(A-B)+1 := by
  have := mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) (sub_nonneg.mpr hAB)
  linarith

/-- Exact boundary of the hypothesis needed by weighted two-level counting. -/
theorem coefficient_two_level_iff {K : ℕ} {a d : ℝ}
    (hK : 0 < K) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    2*beta K a d ≤ alpha a d ↔ d+2 ≤ (K : ℝ) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hd1 : 0 < 2*(d+1) := by positivity
  have hdk : 0 < d+(K : ℝ) := by positivity
  have he : 2*beta K a d = (a+1)/(d+K) := by
    unfold beta
    field_simp
  rw [he, alpha, div_le_div_iff₀ hdk hd1]
  constructor <;> intro h <;> nlinarith

theorem ratio_le_iff {N K m b : ℕ} {A B : ℝ} (hAB : B ≤ A) :
    ratio N K m A B ≤ b ↔
      (N : ℝ)*((m : ℝ)*(A-B)+A) ≤ (b : ℝ)*((K : ℝ)*(A-B)+1) := by
  exact div_le_iff₀ (ratio_denominator_pos K hAB)

theorem ceiling_le_iff {N K m b : ℕ} {A B : ℝ} (hAB : B ≤ A) :
    ⌈ratio N K m A B⌉₊ ≤ b ↔
      (N : ℝ)*((m : ℝ)*(A-B)+A) ≤ (b : ℝ)*((K : ℝ)*(A-B)+1) :=
  Nat.ceil_le.trans (ratio_le_iff hAB)

/-- The exact comparison with ordinary incidence counting. -/
theorem ratio_sub_incidence (N K m : ℕ) {A B : ℝ} (hK : 0 < K) (hAB : B ≤ A) :
    ratio N K m A B - (N : ℝ)*m/K =
      (N : ℝ)*((K : ℝ)*A-m)/((K : ℝ)*((K : ℝ)*(A-B)+1)) := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hh := ne_of_gt (ratio_denominator_pos K hAB)
  unfold ratio
  generalize hz : (K : ℝ)*(A-B)+1 = z
  have hz0 : z ≠ 0 := hz ▸ hh
  field_simp [hk, hz0]
  rw [← hz]
  ring

theorem ratio_le_incidence (N K m : ℕ) {A B : ℝ}
    (hK : 0 < K) (hAB : B ≤ A) (hAm : (K : ℝ)*A ≤ m) :
    ratio N K m A B ≤ (N : ℝ)*m/K := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hh := ratio_denominator_pos K hAB
  have he := ratio_sub_incidence N K m hK hAB
  have hn : (N : ℝ)*((K : ℝ)*A-m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) (sub_nonpos.mpr hAm)
  have := div_nonpos_of_nonpos_of_nonneg hn (mul_pos hk hh).le
  linarith

/-- In the remaining integer range the proposed ratio is no stronger than
incidence counting. The strict integer inequality a<m supplies a+1<=m. -/
theorem fallback_coefficient {K m : ℕ} {a d : ℤ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hKd : (K : ℤ) ≤ d+1) (ham : a < m) :
    alpha a d * K ≤ ((a : ℝ)+1)/2 ∧ ((a : ℝ)+1)/2 ≤ m := by
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hk' : (K : ℝ) ≤ (d : ℝ)+1 := by exact_mod_cast hKd
  have hm' : (a : ℝ)+1 ≤ m := by exact_mod_cast (show a+1 ≤ (m : ℤ) by omega)
  have hp : 0 < 2*((d : ℝ)+1) := by positivity
  constructor
  · unfold alpha
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    nlinarith
  · linarith

end CoveringDesigns.LargeDefect
