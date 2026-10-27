import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! Elementary geometric-sum estimates for the corrected Horsley–Singh Lemma 9.
No covering or geometry definitions are used. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.AffineSchoenheim
open Finset

/-- The finite geometric sum, including the empty sum. -/
def geom (q n : ℕ) : ℕ := ∑ j ∈ range n, q^j

@[simp] theorem geom_zero (q : ℕ) : geom q 0 = 0 := by simp [geom]
@[simp] theorem geom_one (q : ℕ) : geom q 1 = 1 := by simp [geom]

theorem geom_succ (q n : ℕ) : geom q (n+1) = q*geom q n+1 :=
  geom_sum_succ

/-- Exact additive form, without natural subtraction of the numerator. -/
theorem geom_mul_add {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    (q-1)*geom q n+1 = q^n := by
  have h := geom_sum_mul_add (q-1) n
  simpa [Nat.sub_add_cancel hq, geom, Nat.mul_comm] using h

theorem geom_quotient {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    geom q n = (q^n-1)/(q-1) := Nat.geomSum_eq hq n

theorem geom_pos (q : ℕ) {n : ℕ} (hn : 0 < n) : 0 < geom q n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [geom_succ]
  omega

/-- The estimate controlling every interior ceiling correction. -/
theorem index_geom_bound {q t i : ℕ} (hq : 2 ≤ q) (hi : 1 ≤ i) (hit : i ≤ t) :
    i*(q-1)*geom q (t-i)+i ≤ q^(t-1) := by
  have hp : i ≤ q^(i-1) := by
    have h := Nat.lt_pow_self (n := i-1) (by omega : 1 < q)
    omega
  have he : (i-1)+(t-i) = t-1 := by omega
  have hm := Nat.mul_le_mul_right (q^(t-i)) hp
  rw [← pow_add, he] at hm
  have hg := geom_mul_add (by omega : 1 ≤ q) (t-i)
  nlinarith only [hm, hg]

/-- A strict bound for the final ceiling correction on the whole source interval. -/
theorem loss_geom_lt {q m t h : ℕ} (hq : 2 ≤ q) (hm : 2*q+2 ≤ m)
    (ht : 1 ≤ t) (hh : h+3 ≤ 2*q) : h*geom q t < m*q^(t-1) := by
  have hQ : 0 < q-1 := by omega
  have hQeq : q-1+1 = q := Nat.sub_add_cancel (by omega)
  have hP : 0 < q^(t-1) := pow_pos (by omega) _
  have hmul : h*q < m*(q-1) := by nlinarith
  have hp := Nat.mul_lt_mul_of_pos_right hmul hP
  have hg := geom_mul_add (by omega : 1 ≤ q) t
  have he : q^t = q*q^(t-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel ht, pow_succ']
  rw [he] at hg
  have hid : (q-1)*(h*geom q t)+h = h*(q*q^(t-1)) := by
    nlinarith only [hg]
  have hprod : (q-1)*(h*geom q t) < (q-1)*(m*q^(t-1)) := by
    nlinarith only [hp, hid, Nat.zero_le h]
  exact (Nat.mul_lt_mul_left hQ).mp hprod

end CoveringDesigns.AffineSchoenheim
