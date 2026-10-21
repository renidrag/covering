import CoveringDesigns.C18_10_3.Incidence
import CoveringDesigns.C18_10_3.Core

/-! Actual low rows and integer high deficits, for a supplied finite high set.
The covering adapters supply that set from the exhaustive degree profiles. -/
namespace CoveringDesigns.C18_10_3
open Finset Matrix
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Outside (H : Finset α) := {x : α // x ∉ H}

def rowIncidence (C : Family α) (H : Finset α) : Matrix (Outside H) C ℝ :=
  fun x B => if x.val ∈ B.val then 1 else 0

def rowExcess (C : Family α) (H : Finset α) : Matrix (Outside H) (Outside H) ℝ :=
  fun x y => if x = y then 0 else (degree (star C x.val) y.val : ℝ) - 3

def rowDeficit (C : Family α) (H : Finset α) (x : Outside H) : ℕ :=
  ∑ h ∈ H, (degree (star C x.val) h - 3)

theorem outside_card (H : Finset α) : Fintype.card (Outside H) = Fintype.card α - H.card := by
  simp [Outside,Fintype.card_subtype_compl]

theorem pair_self (C : Family α) (p : α) : degree (star C p) p = degree C p := by
  simp [degree,star,filter_filter]

theorem pair_sum_all {C : Family α} {k : ℕ} (hu : Uniform C k) (p : α) :
    ∑ q, degree (star C p) q = k * degree C p :=
  degree_sum_of_uniform (fun B hB => hu B (mem_filter.mp hB).1)

theorem sum_outside (H : Finset α) (f : α → ℕ) :
    (∑ x : Outside H, f x.val) + ∑ x ∈ H, f x = ∑ x, f x := by
  rw [← sum_subtype (univ \ H) (by simp) f]
  exact sum_sdiff (subset_univ H)

theorem row_gram_entry (C : Family α) (H : Finset α) (x y : Outside H) :
    (rowIncidence C H * (rowIncidence C H).transpose) x y =
      (degree (star C x.val) y.val : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowIncidence, degree, star,
    card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  rw [sum_coe_sort C (fun B =>
    (if x.val ∈ B then (1 : ℝ) else 0) * (if y.val ∈ B then 1 else 0))]
  apply sum_congr rfl
  intro B _
  by_cases hx : x.val ∈ B <;> by_cases hy : y.val ∈ B <;> simp [hx,hy]

theorem row_binary (C : Family α) (H : Finset α) :
    ∀ x B, rowIncidence C H x B = 0 ∨ rowIncidence C H x B = 1 := by
  intro x B
  simp only [rowIncidence]
  split_ifs <;> simp

theorem row_sum {C : Family α} {H : Finset α}
    (hlow : ∀ x, x ∉ H → degree C x = 6) (x : Outside H) :
    ∑ B, rowIncidence C H x B = 6 := by
  have hh : (degree C x.val : ℝ) = 6 := by rw [hlow x.val x.property]; norm_num
  rw [← hh]
  simp only [rowIncidence,degree,star,card_eq_sum_ones,sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  exact sum_coe_sort C (fun B => if x.val ∈ B then (1 : ℝ) else 0)

theorem row_gram {C : Family α} {H : Finset α}
    (hlow : ∀ x, x ∉ H → degree C x = 6) :
    rowIncidence C H * (rowIncidence C H).transpose =
      Matrix.diagonal (fun _ => (3 : ℝ)) + rowExcess C H +
        Matrix.of (fun _ _ => (3 : ℝ)) := by
  ext x y
  rw [row_gram_entry]
  by_cases he : x=y
  · subst y
    norm_num [rowExcess,pair_self,hlow x.val x.property]
  · simp [rowExcess,he]

theorem rowExcess_symm (C : Family α) (H : Finset α) (x y : Outside H) :
    rowExcess C H x y = rowExcess C H y x := by
  simp [rowExcess,eq_comm,pair_degree_comm C x.val y.val]

theorem rowExcess_nonneg {C : Family α} {H : Finset α}
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x y : Outside H) :
    0 ≤ rowExcess C H x y := by
  by_cases he : x=y
  · simp [rowExcess,he]
  · have hh := hpair x.val y.val (fun hh => he (Subtype.ext hh))
    simp only [rowExcess,if_neg he]
    exact sub_nonneg.mpr (by exact_mod_cast hh)

theorem rowExcess_diag (C : Family α) (H : Finset α) (x : Outside H) :
    rowExcess C H x x = 0 := by simp [rowExcess]

/-- Deficits are nonnegative integers computed from actual high intersections. -/
theorem rowDeficit_add {C : Family α} {H : Finset α}
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x : Outside H) :
    rowDeficit C H x + 3*H.card = ∑ h ∈ H, degree (star C x.val) h := by
  have he : ∀ h ∈ H, degree (star C x.val) h - 3 + 3 = degree (star C x.val) h := by
    intro h hh
    apply Nat.sub_add_cancel
    exact hpair x.val h (by intro he; exact x.property (he ▸ hh))
  simpa [rowDeficit,sum_add_distrib,Nat.mul_comm] using sum_congr rfl he

theorem row_balance {C : Family α} {H : Finset α}
    (hv : Fintype.card α = 18) (hu : Uniform C 10)
    (hlow : ∀ x, x ∉ H → degree C x = 6)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x : Outside H) :
    (∑ y, rowExcess C H x y) + (rowDeficit C H x : ℝ) = 3 := by
  have hsum := sum_outside H (fun y => degree (star C x.val) y)
  rw [pair_sum_all hu,hlow x.val x.property] at hsum
  have hd := rowDeficit_add hpair x
  have hsumR : (∑ y : Outside H, (degree (star C x.val) y.val : ℝ)) +
      ∑ h ∈ H, (degree (star C x.val) h : ℝ) = 60 := by exact_mod_cast hsum
  have hdR : (rowDeficit C H x : ℝ) + 3*(H.card : ℝ) =
      ∑ h ∈ H, (degree (star C x.val) h : ℝ) := by exact_mod_cast hd
  have hcard : Fintype.card (Outside H) + H.card = 18 := by
    rw [outside_card,hv]
    have hc := card_le_univ H
    rw [hv] at hc
    omega
  have hcardR : (Fintype.card (Outside H) : ℝ) + (H.card : ℝ) = 18 := by exact_mod_cast hcard
  have he (y : Outside H) : rowExcess C H x y =
      (degree (star C x.val) y.val : ℝ) - 3 - (if x=y then 3 else 0) := by
    by_cases hh : x=y
    · subst y
      norm_num [rowExcess,pair_self,hlow x.val x.property]
    · simp [rowExcess,hh]
  simp_rw [he]
  simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,
    sum_ite_eq,mem_univ,ite_true]
  linarith

theorem rowDeficit_le_three {C : Family α} {H : Finset α}
    (hv : Fintype.card α = 18) (hu : Uniform C 10)
    (hlow : ∀ x, x ∉ H → degree C x = 6)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x : Outside H) :
    rowDeficit C H x ≤ 3 := by
  have hh := row_balance hv hu hlow hpair x
  have hn : 0 ≤ ∑ y, rowExcess C H x y := sum_nonneg fun y _ => rowExcess_nonneg hpair x y
  have hd : (rowDeficit C H x : ℝ) ≤ 3 := by linarith
  exact_mod_cast hd

/-- Count the complete deficit budget, including the ordered high-high pairs. -/
theorem deficit_total_identity {C : Family α} (hu : Uniform C 10) (H : Finset α)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    (∑ x : Outside H, rowDeficit C H x) + 3*Fintype.card (Outside H)*H.card +
      (∑ h ∈ H, ∑ g ∈ H, degree (star C h) g) =
      10 * ∑ h ∈ H, degree C h := by
  have hleft := sum_congr rfl (fun (x : Outside H) (_ : x ∈ univ) => rowDeficit_add hpair x)
  simp only [sum_add_distrib,sum_const,card_univ,Nat.nsmul_eq_mul] at hleft
  have hright := sum_congr rfl (fun h (_ : h ∈ H) => sum_outside H (fun x => degree (star C h) x))
  simp only [sum_add_distrib,pair_sum_all hu,← mul_sum] at hright
  have he : (∑ x : Outside H, ∑ h ∈ H, degree (star C x.val) h) =
      ∑ h ∈ H, ∑ x : Outside H, degree (star C h) x.val := by
    rw [sum_comm]
    simp_rw [pair_degree_comm C]
  rw [he] at hleft
  nlinarith

/-- The useful weak-nullity inequality retains the number of zero deficits. -/
theorem low_zero_bound {C : Family α} {H : Finset α}
    (hv : Fintype.card α = 18) (hu : Uniform C 10)
    (hlow : ∀ x, x ∉ H → degree C x = 6)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    2*Fintype.card (Outside H) ≤ 2*C.card +
      (univ.filter (fun x : Outside H => rowDeficit C H x = 0)).card := by
  have hh := BoundaryRank.gram_card_bound (rowIncidence C H) 3 (rowExcess C H)
    (fun x => (rowDeficit C H x : ℝ)) (by norm_num) (rowExcess_symm C H)
    (rowExcess_nonneg hpair) (rowExcess_diag C H) (fun _ => Nat.cast_nonneg _)
    (row_balance hv hu hlow hpair) _
    (TwoKMinusTwoEquality.constant_posSemidef 3 (by norm_num)) (row_gram hlow)
  simpa using hh

end CoveringDesigns.C18_10_3
