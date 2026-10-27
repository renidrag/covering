import CoveringDesigns.LiftingComparison.Algebra
import CoveringDesigns.Multicover.Schoenheim
import Mathlib.Data.Nat.Choose.Basic

/-! Exact arbitrary-seed iteration and the numerical comparison of Remark 14.
Every intermediate ceiling is retained. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.LiftingComparison
open Schoenheim LargeDefect

/-- The existing nested-ceiling recurrence, with an arbitrary numerical seed. -/
abbrev iterate (v k s h : ℕ) : ℕ := Multicover.bound h v k s

@[simp] theorem iterate_zero (v k h : ℕ) : iterate v k 0 h = h := rfl

theorem iterate_succ (v k s h : ℕ) :
    iterate v k (s+1) h = ceilDiv (v*iterate (v-1) (k-1) s h) k := rfl

@[simp] theorem iterate_seed_zero (v k s : ℕ) : iterate v k s 0 = 0 :=
  Multicover.bound_multiplicity_zero v k s

theorem iterate_seed_one (v k s : ℕ) : iterate v k s 1 = Schoenheim.bound v k s :=
  Multicover.bound_one_eq v k s

/-- The binomial-ratio estimate before rounding. -/
theorem binomial_mul_le {v k s : ℕ} (hsk : s ≤ k) (hkv : k ≤ v) (h : ℕ) :
    v.choose s*h ≤ k.choose s*iterate v k s h := by
  induction s generalizing v k with
  | zero => simp
  | succ s ih =>
    have hk : 0 < k := by omega
    have hv : 0 < v := by omega
    have h₁ := Nat.mul_le_mul_left v (ih (by omega : s ≤ k-1) (by omega : k-1 ≤ v-1))
    have h₂ : v*iterate (v-1) (k-1) s h ≤ k*iterate v k (s+1) h :=
      (ceilDiv_le_iff hk).mp (le_refl _)
    have h₃ := Nat.mul_le_mul_left ((k-1).choose s) h₂
    have hvb : v*(v-1).choose s = v.choose (s+1)*(s+1) := by
      simpa only [Nat.sub_add_cancel hv] using Nat.add_one_mul_choose_eq (v-1) s
    have hkb : k*(k-1).choose s = k.choose (s+1)*(s+1) := by
      simpa only [Nat.sub_add_cancel hk] using Nat.add_one_mul_choose_eq (k-1) s
    have hc : (v.choose (s+1)*h)*(s+1) ≤
        (k.choose (s+1)*iterate v k (s+1) h)*(s+1) := by
      calc
        _ = v*((v-1).choose s*h) := by rw [← mul_assoc, hvb]; ring
        _ ≤ (k-1).choose s*(k*iterate v k (s+1) h) := by
          exact h₁.trans (by simpa only [mul_assoc, mul_comm v] using h₃)
        _ = _ := by rw [mul_left_comm, ← mul_assoc, hkb]; ring
    exact (mul_le_mul_iff_left₀ (by omega : 0 < s+1)).mp hc

/-- Collapsing ceilings can only weaken the bound. -/
theorem collapsed_le_iterate {v k s : ℕ} (hsk : s ≤ k) (hkv : k ≤ v) (h : ℕ) :
    ceilDiv (v.choose s*h) (k.choose s) ≤ iterate v k s h :=
  (ceilDiv_le_iff (Nat.choose_pos hsk)).mpr (binomial_mul_le hsk hkv h)

/-- Compatibility between the project's exact division and the natural real ceiling. -/
theorem ceilDiv_eq_natCeil (a b : ℕ) (hb : 0 < b) :
    ceilDiv a b = ⌈(a : ℝ)/b⌉₊ := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  apply Nat.le_antisymm
  · apply (ceilDiv_le_iff hb).mpr
    have hh := Nat.le_ceil ((a : ℝ)/b)
    have := (div_le_iff₀ hb').mp hh
    rw [mul_comm] at this
    exact_mod_cast this
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hb').mpr
    rw [mul_comm]
    exact_mod_cast (ceilDiv_le_iff hb).mp (le_refl (ceilDiv a b))

theorem ceiling_le_collapsed {N K m : ℕ} {A B : ℝ}
    (hK : 0 < K) (hD : 0 < (K : ℝ)*(A-B)+1)
    (hB : (K : ℝ)*B ≤ m+1) :
    ⌈ratio N K m A B⌉₊ ≤ ceilDiv (N*(m+1)) K := by
  rw [ceilDiv_eq_natCeil _ _ hK]
  apply Nat.ceil_mono
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using ratio_le_of_threshold hK hD hB

/-- Remark 14, including the weak threshold. No seed-validity claim is made. -/
theorem remark14 {v k s m : ℕ} {A B : ℝ}
    (hsk : s ≤ k) (hkv : k ≤ v)
    (hD : 0 < (k.choose s : ℝ)*(A-B)+1)
    (hB : (k.choose s : ℝ)*B ≤ m+1) :
    ⌈ratio (v.choose s) (k.choose s) m A B⌉₊ ≤ iterate v k s (m+1) :=
  (ceiling_le_collapsed (Nat.choose_pos hsk) hD hB).trans
    (collapsed_le_iterate hsk hkv (m+1))

/-- Strictness of the real comparison does not assert strictness after rounding. -/
theorem remark14_strict {v k s m : ℕ} {A B : ℝ}
    (hsk : s ≤ k) (hkv : k ≤ v)
    (hD : 0 < (k.choose s : ℝ)*(A-B)+1)
    (hB : (k.choose s : ℝ)*B < m+1) :
    ⌈ratio (v.choose s) (k.choose s) m A B⌉₊ ≤ iterate v k s (m+1) :=
  remark14 hsk hkv hD hB.le

end CoveringDesigns.LiftingComparison
