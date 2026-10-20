import CoveringDesigns.TwoKMinusTwo.Rank

/-! Exact low-point excess counting and regular high-point incidence.
Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusTwoTightening
open Finset Matrix TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

/-- Degree-seven points meeting every degree-six point in exactly three blocks. -/
def regularHigh (C : Family α) : Finset α :=
  univ.filter fun y => degree C y = 7 ∧
    ∀ x : Low C, degree (star C x.val) y = 3

/-- The number of degree-six points with a positive boundary deficit. -/
noncomputable def positiveDeficitCount (C : Family α) : ℕ := by
  classical
  exact (univ.filter fun x : Low C => 0 < deficit C x).card

/-- Actual block-support vector of a point. -/
def supportVector (C : Family α) (y : α) : C → ℝ :=
  fun B => if y ∈ B.val then 1 else 0

@[simp] theorem mem_regularHigh_iff {C : Family α} {y : α} :
    y ∈ regularHigh C ↔ degree C y = 7 ∧
      ∀ x : Low C, degree (star C x.val) y = 3 := by
  simp [regularHigh]

theorem regularHigh_degree {C : Family α} {y : α} (hy : y ∈ regularHigh C) :
    degree C y = 7 := (mem_regularHigh_iff.mp hy).1

theorem regularHigh_pair {C : Family α} {y : α} (hy : y ∈ regularHigh C)
    (x : Low C) : degree (star C x.val) y = 3 :=
  (mem_regularHigh_iff.mp hy).2 x

omit [Fintype α] in
theorem supportVector_binary (C : Family α) (y : α) (B : C) :
    supportVector C y B = 0 ∨ supportVector C y B = 1 := by
  by_cases h : y ∈ B.val <;> simp [supportVector, h]

omit [Fintype α] in
theorem supportVector_sum (C : Family α) (y : α) :
    ∑ B : C, supportVector C y B = (degree C y : ℝ) := by
  simp only [supportVector, degree, star, card_eq_sum_ones, sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_coe_sort C (fun B => if y ∈ B then (1 : ℝ) else 0)]

omit [Fintype α] in
/-- Equality of support vectors is equality of actual block memberships. -/
theorem supportVector_eq_iff (C : Family α) (x y : α) :
    supportVector C x = supportVector C y ↔
      ∀ B ∈ C, (x ∈ B ↔ y ∈ B) := by
  constructor
  · intro h B hB
    have hb := congrFun h ⟨B, hB⟩
    by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;>
      simp_all [supportVector]
  · intro h
    funext B
    simp only [supportVector]
    simp only [h B.val B.property]

/-- Every actual low-point row has six ones. -/
theorem low_row_sum (C : Family α) (x : Low C) :
    ∑ B : C, lowIncidence C x B = (6 : ℝ) := by
  have hx : degree C x.val = 6 := (mem_filter.mp x.property).2
  change (∑ B : C, supportVector C x.val B) = 6
  rw [supportVector_sum, hx]
  norm_num

/-- Multiplication by the low-incidence matrix records the actual pair degrees. -/
theorem supportVector_image (C : Family α) (y : α) :
    lowIncidence C *ᵥ supportVector C y =
      fun x => (degree (star C x.val) y : ℝ) := by
  ext x
  simp only [Matrix.mulVec, dotProduct, lowIncidence, supportVector,
    degree, star, card_eq_sum_ones, sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_coe_sort C (fun B =>
    (if x.val ∈ B then (1 : ℝ) else 0) * (if y ∈ B then 1 else 0))]
  apply sum_congr rfl
  intro B _
  by_cases hx : x.val ∈ B <;> by_cases hy : y ∈ B <;> simp [hx, hy]

/-- All regular high points have the same prescribed low-incidence image. -/
theorem high_image {C : Family α} {y : α} (hy : y ∈ regularHigh C) :
    lowIncidence C *ᵥ supportVector C y = fun _ => (3 : ℝ) := by
  rw [supportVector_image]
  ext x
  rw [regularHigh_pair hy x]
  norm_num

private theorem low_degree (C : Family α) (x : Low C) : degree C x.val = 6 :=
  (mem_filter.mp x.property).2

omit [Fintype α] in
private theorem pair_self (C : Family α) (p : α) :
    degree (star C p) p = degree C p := by simp [degree, star, filter_filter]

/-- A degree-six point has total off-diagonal excess exactly three. -/
theorem low_total_excess {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hu : Uniform C k) (x : Low C) :
    (∑ y, excess C x.val y) = 3 := by
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
  simp_rw [he]
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    sum_ite_eq, mem_univ, ite_true]
  rw [hsR, hvc]
  ring

/-- The deficit is exactly the excess against points outside the low set. -/
theorem deficit_eq_high_sum {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hu : Uniform C k) (x : Low C) :
    deficit C x = ∑ y ∈ univ \ minimumPoints C 6, excess C x.val y := by
  rw [sum_sdiff_eq_sub (subset_univ _), low_total_excess hv hk hu x]
  simp only [deficit, lowExcess, sum_coe_sort]

/-- Only positive deficits contribute, and each contributes at most three. -/
theorem deficit_sum_le {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hu : Uniform C k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    (∑ x : Low C, deficit C x) ≤ 3 * (positiveDeficitCount C : ℝ) := by
  classical
  have hd0 (x : Low C) : 0 ≤ deficit C x :=
    sub_nonneg.mpr (low_row_le hv hk hu hpair x)
  have hd3 (x : Low C) : deficit C x ≤ 3 := by
    apply sub_le_self
    exact sum_nonneg fun y _ => excess_nonneg hpair x.val y.val
  calc
    _ ≤ ∑ x : Low C, if 0 < deficit C x then (3 : ℝ) else 0 := by
      apply sum_le_sum
      intro x _
      by_cases hx : 0 < deficit C x
      · simpa only [ite_eq_left hx] using hd3 x
      · have hz : deficit C x = 0 := le_antisymm (le_of_not_gt hx) (hd0 x)
        simp [hz]
    _ = 3 * (positiveDeficitCount C : ℝ) := by
      rw [sum_ite]
      simp [positiveDeficitCount, mul_comm]

/-- Each nonregular degree-seven point consumes a positive integer excess.
Summing these charges yields the regular-high-point lower bound. -/
theorem regularHigh_count_bound {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hu : Uniform C k) (hdeg : ∀ y, 6 ≤ degree C y)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    8 * Fintype.card α ≤ k * C.card + 2 * (minimumPoints C 6).card +
      3 * positiveDeficitCount C + (regularHigh C).card := by
  classical
  let L := minimumPoints C 6
  let H := univ \ L
  have hsum0 (y : α) : 0 ≤ ∑ x : Low C, excess C x.val y :=
    sum_nonneg fun x _ => excess_nonneg hpair x.val y
  have hp (y : α) : (8 : ℝ) ≤ (degree C y : ℝ) +
      2 * (if y ∈ L then 1 else 0) + (if y ∈ regularHigh C then 1 else 0) +
      (if y ∈ H then ∑ x : Low C, excess C x.val y else 0) := by
    by_cases hl : y ∈ L
    · have hd : degree C y = 6 := (mem_filter.mp hl).2
      have hh : y ∉ H := by simp [H, hl]
      have hr : y ∉ regularHigh C := by
        intro hr
        have := regularHigh_degree hr
        omega
      norm_num [hl, hh, hr, hd]
    · have hd : 7 ≤ degree C y := by
        have hne : degree C y ≠ 6 := by simpa [L, minimumPoints] using hl
        have := hdeg y
        omega
      have hh : y ∈ H := by simp [H, hl]
      by_cases hd7 : degree C y = 7
      · by_cases hr : y ∈ regularHigh C
        · simp only [hd7, Nat.cast_ofNat, ite_eq_right hl, ite_eq_left hr, ite_eq_left hh,
            mul_zero, add_zero]
          linarith [hsum0 y]
        · have hex : ∃ x : Low C, degree (star C x.val) y ≠ 3 := by
            by_contra hn
            push Not at hn
            exact hr (mem_regularHigh_iff.mpr ⟨hd7, hn⟩)
          obtain ⟨x, hx⟩ := hex
          have hxy : x.val ≠ y := by
            intro he
            have hxl : x.val ∈ L := x.property
            exact hl (he ▸ hxl)
          have hfour : 4 ≤ degree (star C x.val) y := by
            have := hpair x.val y hxy
            omega
          have he1 : (1 : ℝ) ≤ excess C x.val y := by
            have hfourR : (4 : ℝ) ≤ degree (star C x.val) y := by
              exact_mod_cast hfour
            simp only [excess, ite_eq_right hxy]
            linarith
          have heS : (1 : ℝ) ≤ ∑ x : Low C, excess C x.val y :=
            he1.trans (single_le_sum (fun z _ => excess_nonneg hpair z.val y) (mem_univ x))
          simp only [hd7, Nat.cast_ofNat, ite_eq_right hl, ite_eq_right hr, ite_eq_left hh,
            mul_zero, add_zero]
          linarith
      · have hd8 : 8 ≤ degree C y := by omega
        have hd8R : (8 : ℝ) ≤ degree C y := by exact_mod_cast hd8
        have hr0 : (0 : ℝ) ≤ if y ∈ regularHigh C then 1 else 0 := by positivity
        simp only [ite_eq_right hl, ite_eq_left hh, mul_zero, add_zero]
        linarith [hsum0 y]
  have hs := sum_le_sum (fun y (_ : y ∈ (univ : Finset α)) => hp y)
  have hsD : (∑ y : α, (degree C y : ℝ)) = (k : ℝ) * C.card := by
    exact_mod_cast degree_sum_of_uniform hu
  have hsL : (∑ y : α, if y ∈ L then (1 : ℝ) else 0) = (L.card : ℝ) := by
    simp
  have hsR : (∑ y : α, if y ∈ regularHigh C then (1 : ℝ) else 0) =
      ((regularHigh C).card : ℝ) := by
    rw [sum_boole]
    simp only [filter_mem_eq_inter, univ_inter]
  have hcharge : (∑ y : α, if y ∈ H then ∑ x : Low C, excess C x.val y else 0) =
      ∑ x : Low C, deficit C x := by
    rw [← sum_filter]
    simp only [filter_mem_eq_inter, univ_inter]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    exact (deficit_eq_high_sum hv hk hu x).symm
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul] at hs
  rw [hsD, hsL, hsR, hcharge] at hs
  have hb := deficit_sum_le hv hk hu hpair
  have hfinal : (8 : ℝ) * Fintype.card α ≤ (k : ℝ) * C.card +
      2 * (L.card : ℝ) + 3 * (positiveDeficitCount C : ℝ) +
      ((regularHigh C).card : ℝ) := by linarith
  exact_mod_cast hfinal

end CoveringDesigns.TwoKMinusTwoTightening
