import CoveringDesigns.TwoKMinusTwoTightening.Incidence
import CoveringDesigns.BoundaryRank.Completion
import CoveringDesigns.BoundaryRank.BinaryCompletion
import CoveringDesigns.BoundaryRank.CloneCapacity

/-! Low-corank support completion excludes the two checkpoint budgets.
No classification of support components is used. Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.TwoKMinusTwoTightening
open Finset Matrix TwoKMinusTwo BoundaryRank
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

/-- Centering and the positive-deficit budget specialised to actual low rows. -/
theorem low_completion {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hu : Uniform C k) (hb : 12 ≤ C.card)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    (centered (lowIncidence C) 6).rank = (lowIncidence C).rank ∧
    centered (lowIncidence C) 6 *ᵥ (fun _ => (1 : ℝ)) = 0 ∧
    1 ≤ C.card - (lowIncidence C).rank ∧
    (minimumPoints C 6).card + positiveDeficitCount C ≤ 2 * (lowIncidence C).rank := by
  classical
  have hc : 0 < Fintype.card C := by simp only [Fintype.card_coe]; omega
  have hcenter : (6 : ℝ)^2 ≤ (Fintype.card C : ℝ)*3 := by
    have hbR : (12 : ℝ) ≤ C.card := by exact_mod_cast hb
    simp only [Fintype.card_coe]
    nlinarith
  have h := centered_completion (lowIncidence C) 6 3 3 (lowExcess C) (deficit C)
    (by norm_num) (by norm_num) hc (by
      intro x y
      simp [lowExcess, excess, eq_comm, pair_degree_comm C x.val y.val])
    (fun x y => excess_nonneg hpair x.val y.val)
    (by intro x; simp [lowExcess, excess])
    (fun x => sub_nonneg.mpr (low_row_le hv hk hu hpair x))
    (by intro x; simp [deficit]) (low_row_sum C) low_gram hcenter
  simpa only [Fintype.card_coe, positiveDeficitCount] using h

/-- Centered images of regular high points are identical. -/
theorem regularHigh_centered_image {C : Family α} {y : α}
    (hy : y ∈ regularHigh C) :
    centered (lowIncidence C) 6 *ᵥ supportVector C y =
      fun _ => 3 - (6 / (Fintype.card C : ℝ))*7 := by
  rw [centered, Matrix.sub_mulVec, high_image hy]
  funext x
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [← mul_sum, supportVector_sum, regularHigh_degree hy]
  norm_num

/-- At column corank one, regular high points have at most one support. -/
theorem regularHigh_supports_le_one {C : Family α}
    (hzero : centered (lowIncidence C) 6 *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hb : 0 < C.card)
    (hrank : C.card - (centered (lowIncidence C) 6).rank ≤ 1) :
    ((regularHigh C).image (supportVector C)).card ≤ 1 := by
  classical
  have h := completion_card_le_one (X := ↥(regularHigh C))
    (centered (lowIncidence C) 6) hzero (by simpa using hb)
    (by simpa using hrank) (fun y => supportVector C y.val)
    (fun _ => 3 - (6 / (Fintype.card C : ℝ))*7)
    (fun y => regularHigh_centered_image y.property) 7
    (fun y => by rw [supportVector_sum, regularHigh_degree y.property]; norm_num)
  have heq : (univ.image fun y : ↥(regularHigh C) => supportVector C y.val) =
      (regularHigh C).image (supportVector C) := by
    ext w
    simp
  rwa [heq] at h

/-- At column corank two, regular high points have at most two supports. -/
theorem regularHigh_supports_le_two {C : Family α}
    (hzero : centered (lowIncidence C) 6 *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hb : 0 < C.card)
    (hrank : C.card - (centered (lowIncidence C) 6).rank ≤ 2) :
    ((regularHigh C).image (supportVector C)).card ≤ 2 := by
  classical
  have h := binary_completion_card_le_two (X := ↥(regularHigh C))
    (centered (lowIncidence C) 6) hzero (by simpa using hb)
    (by simpa using hrank) (fun y => supportVector C y.val)
    (fun y B => supportVector_binary C y.val B)
    (fun _ => 3 - (6 / (Fintype.card C : ℝ))*7)
    (fun y => regularHigh_centered_image y.property) 7
    (fun y => by rw [supportVector_sum, regularHigh_degree y.property]; norm_num)
  have heq : (univ.image fun y : ↥(regularHigh C) => supportVector C y.val) =
      (regularHigh C).image (supportVector C) := by
    ext w
    simp
  rwa [heq] at h

/-- Five points per support at the lower endpoint. -/
theorem regularHigh_card_le_five_mul {C : Family α}
    (hv : Fintype.card α = 32) (hu : Uniform C 17)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    (regularHigh C).card ≤ 5 * ((regularHigh C).image (supportVector C)).card := by
  classical
  apply card_le_mul_image_card
  intro w hw
  apply clone_card_le_five C _ hv hu
  · intro x hx
    exact regularHigh_degree (mem_filter.mp hx).1
  · intro x hx y hy
    have heq : supportVector C x = supportVector C y :=
      (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
    exact (supportVector_eq_iff C x y).mp heq
  · exact hpair

/-- Ten points per support at the exactness endpoint. -/
theorem regularHigh_card_le_ten_mul {C : Family α}
    (hv : Fintype.card α = 68) (hu : Uniform C 35)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    (regularHigh C).card ≤ 10 * ((regularHigh C).image (supportVector C)).card := by
  classical
  apply card_le_mul_image_card
  intro w hw
  apply clone_card_le_ten C _ hv hu
  · intro x hx
    exact regularHigh_degree (mem_filter.mp hx).1
  · intro x hx y hy
    have heq : supportVector C x = supportVector C y :=
      (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
    exact (supportVector_eq_iff C x y).mp heq
  · exact hpair

/-- No twelve-block ordinary uniform family with the stated actual floors.
Triple coverage is needed only later to derive these floors. -/
theorem no_twelve_32_17 {C : Family α} (hv : Fintype.card α = 32)
    (hu : Uniform C 17) (hb : C.card = 12)
    (hdeg : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) : False := by
  classical
  obtain ⟨hrank, hzero, hu1, hbudget⟩ := low_completion (k := 17)
    (by omega) (by norm_num) hu (by omega) hpair
  have hi := minimum_points_bound hu hdeg
  have hc := regularHigh_count_bound (k := 17) (by omega) (by norm_num) hu hdeg hpair
  have hwidth : (lowIncidence C).rank ≤ C.card := by
    simpa using (lowIncidence C).rank_le_card_width
  have hu2 : C.card - (lowIncidence C).rank ≤ 2 := by
    rw [hv, hb] at hi
    omega
  have hf : 6 * (C.card - (lowIncidence C).rank) ≤ (regularHigh C).card := by
    rw [hv, hb] at hi hc
    omega
  have hcap := regularHigh_card_le_five_mul hv hu hpair
  by_cases h1 : C.card - (lowIncidence C).rank ≤ 1
  · have hs := regularHigh_supports_le_one hzero (by omega) (by rwa [hrank])
    omega
  · have hs := regularHigh_supports_le_two hzero (by omega) (by rwa [hrank])
    omega

/-- No thirteen-block ordinary uniform family with the stated actual floors. -/
theorem no_thirteen_68_35 {C : Family α} (hv : Fintype.card α = 68)
    (hu : Uniform C 35) (hb : C.card = 13)
    (hdeg : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) : False := by
  classical
  obtain ⟨hrank, hzero, hu1, hbudget⟩ := low_completion (k := 35)
    (by omega) (by norm_num) hu (by omega) hpair
  have hi := minimum_points_bound hu hdeg
  have hc := regularHigh_count_bound (k := 35) (by omega) (by norm_num) hu hdeg hpair
  have hwidth : (lowIncidence C).rank ≤ C.card := by
    simpa using (lowIncidence C).rank_le_card_width
  have hu2 : C.card - (lowIncidence C).rank ≤ 2 := by
    rw [hv, hb] at hi
    omega
  have hf : 32 + 6 * (C.card - (lowIncidence C).rank) ≤ (regularHigh C).card := by
    rw [hv, hb] at hi hc
    omega
  have hcap := regularHigh_card_le_ten_mul hv hu hpair
  have hs := regularHigh_supports_le_two hzero (by omega) (by rwa [hrank])
  omega

end CoveringDesigns.TwoKMinusTwoTightening
