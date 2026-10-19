import CoveringDesigns.Weighted.PartitionedRank
import CoveringDesigns.TwoKMinusTwo.Rank

/-! The variable-offset row allowance and strict partitioned rank.
Only the generic incidence Gram identity from the old rank module is used. -/
namespace CoveringDesigns.TwoKMinusCGeneral
open Finset Matrix TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α] {c k : ℕ}

def integerExcess (C : Family α) (x y : α) : ℤ :=
  if x=y then 0 else (degree (star C x) y : ℤ)-3

omit [Fintype α] in
theorem integerExcess_cast (C : Family α) (x y : α) :
    (integerExcess C x y : ℝ)=excess C x y := by
  by_cases h : x=y <;> simp [integerExcess,excess,h]

theorem integerExcess_nonneg {C : Family α}
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x y : α) :
    0 ≤ integerExcess C x y := by
  have h := excess_nonneg hpair x y
  rw [← integerExcess_cast] at h
  exact_mod_cast h

/-- The full excess row has sum 3(c−1); restricting to low points only decreases it. -/
theorem low_row_le {C : Family α} (hv : Fintype.card α+c=2*k)
    (hu : Uniform C k) (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (x : Low C) : (∑ y : Low C, integerExcess C x.val y.val) ≤ 3*((c : ℤ)-1) := by
  have hx : degree C x.val=6 := (mem_filter.mp x.property).2
  have hs := degree_sum_of_uniform (C := star C x.val)
    (fun B hB => hu B (mem_filter.mp hB).1)
  change (∑ y, degree (star C x.val) y)=k*degree C x.val at hs
  rw [hx] at hs
  have hsZ : (∑ y, (degree (star C x.val) y : ℤ))=(k : ℤ)*6 := by exact_mod_cast hs
  have hvZ : (Fintype.card α : ℤ)+c=2*k := by exact_mod_cast hv
  have hself : degree (star C x.val) x.val=6 := by
    simpa [degree,star,filter_filter] using hx
  have he (y : α) : integerExcess C x.val y =
      (degree (star C x.val) y : ℤ)-3-(if x.val=y then 3 else 0) := by
    by_cases h : x.val=y
    · subst y; norm_num [integerExcess,hself]
    · simp [integerExcess,h]
  have ht : (∑ y, integerExcess C x.val y)=3*((c : ℤ)-1) := by
    simp_rw [he]
    simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,
      sum_ite_eq,mem_univ,ite_true]
    rw [hsZ]
    linarith
  rw [← ht,sum_coe_sort]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by
    intro y _ _
    exact integerExcess_nonneg hpair x.val y)

/-- No coverage or block budget is needed once the actual pair floor is supplied. -/
theorem low_card_le {C : Family α} (hv : Fintype.card α+c=2*k) (hc : 2≤c)
    (hu : Uniform C k) (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    (minimumPoints C 6).card ≤ c*C.card := by
  have hpsd : (Matrix.of (fun (_ _ : Low C) => (3 : ℝ))).PosSemidef := by
    convert (Horsley.ones_posSemidef (ι := Low C)).smul (show (0 : ℝ)≤3 by norm_num) using 1
    ext x y
    change (3 : ℝ)=3*1
    ring
  have hg : lowIncidence C*(lowIncidence C).transpose =
      Matrix.diagonal (fun _ => (3 : ℝ)) +
      Matrix.of (fun (x y : Low C) => (integerExcess C x.val y.val : ℝ)) +
      Matrix.of (fun _ _ => (3 : ℝ)) := by
    have he : Matrix.of (fun (x y : Low C) => (integerExcess C x.val y.val : ℝ)) =
        lowExcess C := by
      ext x y
      exact integerExcess_cast C x.val y.val
    rw [he]
    exact low_gram
  have hb := Weighted.partitioned_gram_card_le (lowIncidence C)
    (fun (x y : Low C) => integerExcess C x.val y.val)
    (Matrix.of (fun _ _ => (3 : ℝ))) (q := c) (by omega) (by norm_num)
    (D := 3*((c : ℤ)-1))
    (by intro x y; simp [integerExcess,eq_comm,pair_degree_comm C x.val y.val])
    (fun x y => integerExcess_nonneg hpair x.val y.val)
    (by intro x; simp [integerExcess]) (low_row_le hv hu hpair)
    (by push_cast; linarith) hpsd hg
  simpa only [Fintype.card_coe] using hb

/-- Conditional incidence inequality: both floors refer to this actual family. -/
theorem conditional_rank {C : Family α} (hv : Fintype.card α+c=2*k) (hc : 2≤c)
    (hu : Uniform C k) (hpoint : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    7*Fintype.card α ≤ (k+c)*C.card := by
  have hl := low_card_le hv hc hu hpair
  have hi := minimum_points_bound hu hpoint
  nlinarith

end CoveringDesigns.TwoKMinusCGeneral
