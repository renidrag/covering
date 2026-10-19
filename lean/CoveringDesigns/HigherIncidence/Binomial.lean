import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.NormNum

/-! General integer binomial inversion used in Horsley–Singh Lemma 2.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.HigherIncidence
open Finset

/-- The triangular binomial cancellation kernel, including indices above n. -/
theorem binomial_kernel (n i : ℕ) :
    ∑ j ∈ range (n+1), (-1 : ℤ)^(i+j) * n.choose j * j.choose i =
      if i=n then 1 else 0 := by
  by_cases hi : i ≤ n
  · have hsplit : n+1 = i+(n-i+1) := by omega
    rw [hsplit, sum_range_add]
    have hz : (∑ j ∈ range i, (-1 : ℤ)^(i+j)*n.choose j*j.choose i) = 0 := by
      apply sum_eq_zero
      intro j hj
      simp [Nat.choose_eq_zero_of_lt (mem_range.mp hj)]
    rw [hz, zero_add]
    have he (j : ℕ) : (-1 : ℤ)^(i+(i+j))*n.choose (i+j)*(i+j).choose i =
        (n.choose i : ℤ)*((-1 : ℤ)^j*(n-i).choose j) := by
      have hc := Nat.choose_mul (n := n) (k := i+j) (s := i) (by omega)
      have hc' : (n.choose (i+j) : ℤ)*(i+j).choose i =
          (n.choose i : ℤ)*(n-i).choose j := by exact_mod_cast (by simpa using hc : n.choose (i+j)*(i+j).choose i = n.choose i*(n-i).choose j)
      rw [show i+(i+j)=2*i+j by omega, pow_add, pow_mul]
      norm_num
      rw [mul_assoc, hc']
      ring
    simp_rw [he]
    rw [← mul_sum, Int.alternating_sum_range_choose]
    by_cases h : i=n
    · subst i
      simp
    · simp [h, show n-i ≠ 0 by omega]
  · have hni : n < i := by omega
    rw [ite_eq_right (by omega)]
    apply sum_eq_zero
    intro j hj
    simp [Nat.choose_eq_zero_of_lt (show j<i by have := mem_range.mp hj; omega)]

/-- Lemma 2 in the source's closed-interval notation. -/
theorem binomial_cancellation {n i : ℕ} (_hi : i ≤ n) :
    ∑ j ∈ Icc i n, (-1 : ℤ)^(i+j)*n.choose j*j.choose i =
      if i=n then 1 else 0 := by
  rw [← binomial_kernel n i]
  apply sum_subset
  · intro j hj
    exact mem_range.mpr (by have := mem_Icc.mp hj; omega)
  · intro j hj hn
    have hjn := mem_range.mp hj
    have hji : j<i := by simp only [mem_Icc] at hn; omega
    simp [Nat.choose_eq_zero_of_lt hji]

/-- The alternating binomial transform, with values in the integers. -/
def coefficient (s : ℕ) (b : ℕ → ℕ) (j : ℕ) : ℤ :=
  ∑ i ∈ range (j+1), (-1 : ℤ)^(i+j)*j.choose i*b (2*s-i)

/-- Inverting the transform; vanishing binomial coefficients permit any upper
limit s at least the intersection size. -/
theorem coefficient_inversion (s : ℕ) (b : ℕ → ℕ) {ℓ : ℕ} (hl : ℓ ≤ s) :
    ∑ j ∈ range (s+1), coefficient s b j * ℓ.choose j = (b (2*s-ℓ) : ℤ) := by
  have he (j : ℕ) (hj : j ∈ range (s+1)) :
      coefficient s b j = ∑ i ∈ range (s+1),
        (-1 : ℤ)^(i+j)*j.choose i*b (2*s-i) := by
    unfold coefficient
    apply sum_subset
    · exact range_mono (by have := mem_range.mp hj; omega)
    · intro i hi hij
      simp only [mem_range, not_lt] at hij
      simp [Nat.choose_eq_zero_of_lt (show j<i by omega)]
  have expand : (∑ j ∈ range (s+1), coefficient s b j * ℓ.choose j) =
      ∑ j ∈ range (s+1), ∑ i ∈ range (s+1),
        (-1 : ℤ)^(i+j)*j.choose i*b (2*s-i)*ℓ.choose j := by
    apply sum_congr rfl
    intro j hj
    rw [he j hj, sum_mul]
  rw [expand, sum_comm]
  have hk (i : ℕ) : (∑ j ∈ range (s+1),
      (-1 : ℤ)^(i+j)*j.choose i*b (2*s-i)*ℓ.choose j) =
      (if i=ℓ then 1 else 0)*(b (2*s-i) : ℤ) := by
    have hsum : (∑ j ∈ range (s+1), (-1 : ℤ)^(i+j)*ℓ.choose j*j.choose i) =
        ∑ j ∈ range (ℓ+1), (-1 : ℤ)^(i+j)*ℓ.choose j*j.choose i := by
      symm
      apply sum_subset (range_mono (by omega))
      intro j hj hjl
      simp only [mem_range, not_lt] at hjl
      simp [Nat.choose_eq_zero_of_lt (show ℓ<j by omega)]
    calc
      _ = (∑ j ∈ range (s+1), (-1 : ℤ)^(i+j)*ℓ.choose j*j.choose i)*b (2*s-i) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hsum, binomial_kernel]
  simp_rw [hk]
  simp [show ℓ < s+1 by omega]

end CoveringDesigns.HigherIncidence
