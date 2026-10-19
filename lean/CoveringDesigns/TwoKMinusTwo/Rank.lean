import CoveringDesigns.TwoKMinusTwo.Incidence
import CoveringDesigns.BoundaryRank.Nullity

/-! The boundary-rank argument on all degree-six points. -/
namespace CoveringDesigns.TwoKMinusTwo
open Finset Matrix
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

abbrev Low (C : Family α) := ↥(minimumPoints C 6)

def lowIncidence (C : Family α) : Matrix (Low C) C ℝ :=
  fun x B => if x.val ∈ B.val then 1 else 0

def excess (C : Family α) (x y : α) : ℝ :=
  if x = y then 0 else (degree (star C x) y : ℝ) - 3

def lowExcess (C : Family α) : Matrix (Low C) (Low C) ℝ :=
  fun x y => excess C x.val y.val

def deficit (C : Family α) (x : Low C) : ℝ := 3 - ∑ y, lowExcess C x y

private theorem low_degree (C : Family α) (x : Low C) : degree C x.val = 6 :=
  (mem_filter.mp x.property).2

private theorem pair_self (C : Family α) (p : α) :
    degree (star C p) p = degree C p := by simp [degree, star, filter_filter]

theorem excess_nonneg {C : Family α}
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x y : α) :
    0 ≤ excess C x y := by
  by_cases he : x=y
  · simp [excess, he]
  · have h := hpair x y he
    simp only [excess, if_neg he]
    exact sub_nonneg.mpr (by exact_mod_cast h)

theorem low_row_le {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hu : Uniform C k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x : Low C) :
    (∑ y, lowExcess C x y) ≤ 3 := by
  have hs := degree_sum_of_uniform (C := star C x.val)
    (fun B hB => hu B (mem_filter.mp hB).1)
  change (∑ y, degree (star C x.val) y) = k * degree C x.val at hs
  rw [low_degree] at hs
  have hsR : (∑ y, (degree (star C x.val) y : ℝ)) = (k : ℝ)*6 := by
    exact_mod_cast hs
  have hvc : (Fintype.card α : ℝ) = 2*(k : ℝ)-2 := by
    have he : Fintype.card α + 2 = 2*k := by omega
    have heR : (Fintype.card α : ℝ)+2=2*(k : ℝ) := by exact_mod_cast he
    linarith
  have he (y : α) : excess C x.val y =
      (degree (star C x.val) y : ℝ)-3-(if x.val=y then 3 else 0) := by
    by_cases h : x.val=y
    · subst y
      norm_num [excess, pair_self, low_degree]
    · simp [excess, h]
  have htotal : (∑ y, excess C x.val y) = 3 := by
    simp_rw [he]
    simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
      sum_ite_eq, mem_univ, ite_true]
    rw [hsR, hvc]
    ring
  rw [← htotal]
  change (∑ y : ↥(minimumPoints C 6), excess C x.val y.val) ≤ _
  rw [sum_coe_sort]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by
    intro y _ _
    exact excess_nonneg hpair x.val y)

theorem low_gram {C : Family α} :
    lowIncidence C * (lowIncidence C).transpose =
      Matrix.diagonal (fun _ => (3 : ℝ)) + lowExcess C +
        Matrix.of (fun _ _ => (3 : ℝ)) := by
  have he (x y : Low C) : (lowIncidence C * (lowIncidence C).transpose) x y =
      (degree (star C x.val) y.val : ℝ) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, lowIncidence, degree, star,
      card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    rw [sum_coe_sort C (fun B =>
      (if x.val ∈ B then (1 : ℝ) else 0) * (if y.val ∈ B then 1 else 0))]
    apply sum_congr rfl
    intro B _
    by_cases hx : x.val ∈ B <;> by_cases hy : y.val ∈ B <;> simp [hx,hy]
  ext x y
  rw [he]
  by_cases h : x=y
  · subst y
    norm_num [lowExcess, excess, pair_self, low_degree]
  · have hv : x.val ≠ y.val := fun e => h (Subtype.ext e)
    simp [lowExcess, excess, h, hv]

private theorem three_ones_psd {ι : Type*} [Fintype ι] :
    Matrix.PosSemidef (Matrix.of (fun (_ _ : ι) => (3 : ℝ))) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp
  · intro x
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply]
    have he : (∑ i, x i * ∑ j, 3 * x j) = 3 * (∑ i, x i)^2 := by
      rw [← mul_sum, ← sum_mul]
      ring
    rw [he]
    positivity

/-- Reusable row bound; there need not be a unique high point. -/
theorem low_card_le {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hu : Uniform C k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    (minimumPoints C 6).card ≤ 2*C.card := by
  have h := BoundaryRank.gram_card_bound (lowIncidence C) 3 (lowExcess C) (deficit C)
    (by norm_num) (by
      intro x y
      simp [lowExcess, excess, eq_comm, pair_degree_comm C x.val y.val])
    (fun x y => excess_nonneg hpair x.val y.val)
    (by intro x; simp [lowExcess,excess])
    (fun x => sub_nonneg.mpr (low_row_le hv hk hu hpair x))
    (by intro x; simp [deficit])
    (Matrix.of (fun _ _ => (3 : ℝ))) three_ones_psd low_gram
  have hz : (univ.filter (fun x : Low C => deficit C x=0)).card ≤
      Fintype.card (Low C) := (card_filter_le _ _).trans_eq card_univ
  have hc : Fintype.card (Low C) = (minimumPoints C 6).card := Fintype.card_coe _
  have hb : Fintype.card C = C.card := Fintype.card_coe _
  rw [hc,hb] at h
  rw [hc] at hz
  omega

/-- Conditional rank inequality with its structural premise explicit. -/
theorem conditional_rank {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 9 ≤ k) (hC : IsCover C k 3)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    14*(k-1) ≤ (k+2)*C.card := by
  have hr := low_card_le hv (by omega) hC.1 hpair
  have hi := minimum_points_bound hC.1 (degree_ge_six hv hk hC)
  rw [hv] at hi
  have hs : k-1+1=k := by omega
  have ht : 2*k-2+2=2*k := by omega
  nlinarith

end CoveringDesigns.TwoKMinusTwo
