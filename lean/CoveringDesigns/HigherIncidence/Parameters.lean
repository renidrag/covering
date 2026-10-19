import CoveringDesigns.HigherIncidence.Counting

/-! The exact numerical hypotheses of Horsley–Singh Lemma 3, for λ=1 and
arbitrary admissible s. Universal smaller-cover bounds are supplied separately. -/
namespace CoveringDesigns.HigherIncidence
open Finset

structure Parameters (v k t s : ℕ) (b : ℕ → ℕ) : Prop where
  order_pos : 1 ≤ s
  strength : 2*s ≤ t
  strength_lt : t < k
  block_lt : k < v
  positive : ∀ i, s ≤ i → i ≤ 2*s → 0 < b i
  seed : Schoenheim.bound (v-2*s) (k-2*s) (t-2*s) ≤ b (2*s)
  step : ∀ i, s ≤ i → i < 2*s → Schoenheim.ceilDiv ((v-i)*b (i+1)) (k-i) ≤ b i
  coefficients : ∀ j, j ≤ s → 0 ≤ coefficient s b j

theorem Parameters.denominator_pos {v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters v k t s b) {i : ℕ} (hi : i ≤ 2*s) : 0 < k-i := by
  have := h.strength
  have := h.strength_lt
  omega

theorem Parameters.recurrence {v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters v k t s b) {i : ℕ} (hs : s ≤ i) (hi : i < 2*s) :
    (v-i)*b (i+1) ≤ (k-i)*b i :=
  (Schoenheim.ceilDiv_le_iff (h.denominator_pos hi.le)).mp (h.step i hs hi)

/-- Iterating the recurrence with binomial coefficients avoids rational
division and factorial cancellation. -/
theorem Parameters.binomial_recurrence {v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters v k t s b) {r : ℕ} (hr : r ≤ s) :
    (v-s).choose r*b (s+r) ≤ (k-s).choose r*b s := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ih := ih (by omega)
    have hstep := h.recurrence (i := s+r) (by omega) (by omega)
    have hv := Nat.choose_succ_right_eq (v-s) r
    have hk := Nat.choose_succ_right_eq (k-s) r
    simp only [Nat.sub_sub] at hv hk
    have h₁ := Nat.mul_le_mul_left ((v-s).choose r) hstep
    have h₂ := Nat.mul_le_mul_left (k-(s+r)) ih
    have ev := congrArg (fun z : ℕ => z*b (s+(r+1))) hv
    have ek := congrArg (fun z : ℕ => z*b s) hk
    have hh : (r+1)*((v-s).choose (r+1)*b (s+(r+1))) ≤
        (r+1)*((k-s).choose (r+1)*b s) := by
      have hs : s+r+1 = s+(r+1) := by omega
      rw [hs] at h₁
      nlinarith only [h₁, h₂, ev, ek]
    exact Nat.le_of_mul_le_mul_left hh (by omega)

/-- The Vandermonde sum with its diagonal term separated. -/
theorem vandermonde_off_diagonal {k s : ℕ} (hs : s ≤ k) :
    (∑ i ∈ range s, s.choose i*(k-s).choose (s-i))+1 = k.choose s := by
  have hh := Nat.add_choose_eq s (k-s) s
  rw [Nat.add_sub_of_le hs, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ] at hh
  simpa using hh.symm

/-- Nonnegative defect follows from the ceiling recurrences, even when no
subset has multiplicity b_s (or no covering exists). -/
theorem Parameters.defect_nonneg {v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters v k t s b) : 0 ≤ defect v k s b := by
  have ht := h.strength
  have htk := h.strength_lt
  have hs : s ≤ k := by omega
  have hsum : (∑ i ∈ range s, s.choose i*(v-s).choose (s-i)*b (2*s-i)) ≤
      (∑ i ∈ range s, s.choose i*(k-s).choose (s-i))*b s := by
    rw [sum_mul]
    apply sum_le_sum
    intro i hi
    have hi' : i < s := mem_range.mp hi
    have hh := h.binomial_recurrence (r := s-i) (by omega)
    have he : s+(s-i)=2*s-i := by omega
    rw [he] at hh
    simpa only [mul_assoc] using Nat.mul_le_mul_left (s.choose i) hh
  have hz : (∑ i ∈ range s, (s.choose i : ℤ)*(v-s).choose (s-i)*b (2*s-i)) ≤
      (∑ i ∈ range s, (s.choose i : ℤ)*(k-s).choose (s-i))*(b s : ℤ) := by
    exact_mod_cast hsum
  have hv : (∑ i ∈ range s, (s.choose i : ℤ)*(k-s).choose (s-i))+1 =
      (k.choose s : ℤ) := by exact_mod_cast vandermonde_off_diagonal hs
  unfold defect
  nlinarith only [hz, hv]

theorem Parameters.diagonal_pos {v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters v k t s b) (hd : defect v k s b < coefficient s b s) :
    0 < coefficient s b s := lt_of_le_of_lt h.defect_nonneg hd

/-- The positive part retains a strictly positive constant Gram term. -/
theorem Parameters.diagonal_lt {v k t s : ℕ} {b : ℕ → ℕ}
    (h : Parameters v k t s b) : coefficient s b s < (b s : ℤ) := by
  have hf := coefficient_inversion s b (le_refl s)
  rw [show 2*s-s=s by omega, sum_range_succ] at hf
  simp only [Nat.choose_self, Nat.cast_one, mul_one] at hf
  have hz : coefficient s b 0 = (b (2*s) : ℤ) := by simp [coefficient]
  have hpos := h.positive (2*s) (by omega) (by omega)
  have hmem : 0 ∈ range s := mem_range.mpr (by have := h.order_pos; omega)
  have hlo := single_le_sum (f := fun j => coefficient s b j*(s.choose j : ℤ))
    (fun j hj => mul_nonneg (h.coefficients j (by have := mem_range.mp hj; omega))
      (Int.natCast_nonneg _)) hmem
  simp only [hz, Nat.choose_zero_right, Nat.cast_one, mul_one] at hlo
  omega

end CoveringDesigns.HigherIncidence
