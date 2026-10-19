import CoveringDesigns.C20_11_3.Incidence
import CoveringDesigns.BoundaryRank.Nullity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
The incidence matrix on the nineteen degree-six points. The excess and
deficit identities here use actual ordinary blocks, not an abstract Gram
matrix assumption. The boundary-rank interface is applied below.
-/

namespace CoveringDesigns.C20_11_3

open Finset Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Low (h : α) := {x : α // x ≠ h}

def lowIncidence (C : Family α) (h : α) : Matrix (Low h) C ℝ :=
  fun x B => if x.val ∈ B.val then 1 else 0

def lowExcess (C : Family α) (h : α) : Matrix (Low h) (Low h) ℝ :=
  fun x y => if x = y then 0 else (degree (star C x.val) y.val : ℝ) - 3

def highDeficit (C : Family α) (h : α) (x : Low h) : ℝ :=
  (degree (star C x.val) h : ℝ) - 3

omit [Fintype α] in
private theorem rank_pair_self (C : Family α) (p : α) :
    degree (star C p) p = degree C p := by
  simp [degree, star, filter_filter]

private theorem rank_pair_sum {C : Family α} {k : ℕ} (hu : Uniform C k) (p : α) :
    ∑ q, degree (star C p) q = k * degree C p := by
  apply degree_sum_of_uniform
  intro B hB
  exact hu B (mem_filter.mp hB).1

theorem low_card (hv : Fintype.card α = 20) (h : α) :
    Fintype.card (Low h) = 19 := by
  simp [Low, complement_point_card, hv]

omit [Fintype α] in
theorem lowIncidence_gram_entry (C : Family α) (h : α) (x y : Low h) :
    (lowIncidence C h * (lowIncidence C h).transpose) x y =
      (degree (star C x.val) y.val : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, lowIncidence, degree, star,
    card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  rw [sum_coe_sort C (fun B =>
    (if x.val ∈ B then (1 : ℝ) else 0) * (if y.val ∈ B then 1 else 0))]
  apply sum_congr rfl
  intro B _
  by_cases hx : x.val ∈ B <;> by_cases hy : y.val ∈ B <;> simp [hx, hy]

omit [Fintype α] in
theorem low_gram {C : Family α} {h : α}
    (hlow : ∀ x, x ≠ h → degree C x = 6) :
    lowIncidence C h * (lowIncidence C h).transpose =
      Matrix.diagonal (fun _ => (3 : ℝ)) + lowExcess C h +
        Matrix.of (fun _ _ => (3 : ℝ)) := by
  ext x y
  rw [lowIncidence_gram_entry]
  by_cases he : x = y
  · subst y
    norm_num [lowExcess, rank_pair_self, hlow x.val x.property]
  · simp [lowExcess, he, sub_add_cancel]

omit [Fintype α] in
theorem lowExcess_symm (C : Family α) (h : α) (x y : Low h) :
    lowExcess C h x y = lowExcess C h y x := by
  by_cases he : x = y
  · subst y; rfl
  · simp [lowExcess, he, Ne.symm he, pair_degree_comm C x.val y.val]

omit [Fintype α] in
theorem lowExcess_nonneg {C : Family α} {h : α}
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x y : Low h) :
    0 ≤ lowExcess C h x y := by
  by_cases he : x = y
  · simp [lowExcess, he]
  · have hp := hpair x.val y.val (fun e => he (Subtype.ext e))
    simp only [lowExcess, ite_eq_right he]
    exact sub_nonneg.mpr (by exact_mod_cast hp)

omit [Fintype α] in
theorem lowExcess_diagonal (C : Family α) (h : α) (x : Low h) :
    lowExcess C h x x = 0 := by simp [lowExcess]

omit [Fintype α] in
theorem highDeficit_nonneg {C : Family α} {h : α}
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x : Low h) :
    0 ≤ highDeficit C h x := by
  have hp := hpair x.val h x.property
  exact sub_nonneg.mpr (by exact_mod_cast hp)

theorem low_row_identity {C : Family α} {h : α}
    (hv : Fintype.card α = 20) (hu : Uniform C 11)
    (hlow : ∀ x, x ≠ h → degree C x = 6) (x : Low h) :
    (∑ y, lowExcess C h x y) + highDeficit C h x = 3 := by
  have hsum := rank_pair_sum hu x.val
  rw [hlow x.val x.property] at hsum
  have hsumR : (∑ y : α, (degree (star C x.val) y : ℝ)) = 66 := by
    exact_mod_cast hsum
  rw [Fintype.sum_eq_add_sum_subtype_ne _ h] at hsumR
  have he (y : Low h) : lowExcess C h x y =
      (degree (star C x.val) y.val : ℝ) - 3 - (if x = y then 3 else 0) := by
    by_cases hxy : x = y
    · subst y
      norm_num [lowExcess, rank_pair_self, hlow x.val x.property]
    · simp [lowExcess, hxy]
  simp_rw [he]
  simp only [sum_sub_distrib, sum_const, card_univ, low_card hv h, nsmul_eq_mul,
    Nat.cast_ofNat]
  simp only [sum_ite_eq, mem_univ, ite_true]
  unfold highDeficit
  linarith

theorem high_deficit_sum {C : Family α} {h : α}
    (hv : Fintype.card α = 20) (hu : Uniform C 11) (hh : degree C h = 7) :
    ∑ x, highDeficit C h x = 13 := by
  have hsum := rank_pair_sum hu h
  rw [hh] at hsum
  have hsumR : (∑ x : α, (degree (star C h) x : ℝ)) = 77 := by
    exact_mod_cast hsum
  rw [Fintype.sum_eq_add_sum_subtype_ne _ h, rank_pair_self, hh] at hsumR
  norm_num at hsumR
  simp only [highDeficit, sum_sub_distrib, sum_const, card_univ, low_card hv h,
    nsmul_eq_mul, Nat.cast_ofNat]
  simp_rw [pair_degree_comm C _ h]
  linarith

/-- The thirteen-unit deficit, with each entry at most three, leaves at
most fourteen zero entries among nineteen vertices. -/
theorem zero_card_le_fourteen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (δ : ι → ℝ) (hc : Fintype.card ι = 19)
    (hδ : ∀ i, δ i ≤ 3) (hs : ∑ i, δ i = 13) :
    (univ.filter (fun i => δ i = 0)).card ≤ 14 := by
  classical
  let T := univ.filter (fun i => δ i ≠ 0)
  have hsum : (13 : ℝ) ≤ 3 * (T.card : ℝ) := by
    calc
      13 = ∑ i, δ i := hs.symm
      _ ≤ ∑ i, if δ i ≠ 0 then (3 : ℝ) else 0 := by
        apply sum_le_sum
        intro i _
        split_ifs with hi
        · exact hδ i
        · simp_all
      _ = 3 * (T.card : ℝ) := by
        rw [← sum_filter]
        simp only [sum_const, nsmul_eq_mul]
        change (T.card : ℝ) * 3 = 3 * (T.card : ℝ)
        ring
  have ht : 5 ≤ T.card := by
    by_contra hn
    have hh : (T.card : ℝ) ≤ 4 := by exact_mod_cast (show T.card ≤ 4 by omega)
    linarith
  have hpartition := card_filter_add_card_filter_not (s := (univ : Finset ι))
    (fun i => δ i = 0)
  have hpart : (univ.filter (fun i => δ i = 0)).card + T.card = 19 := by
    simpa only [T, card_univ, hc] using hpartition
  omega

theorem highDeficit_zero_card_le {C : Family α} {h : α}
    (hv : Fintype.card α = 20) (hu : Uniform C 11)
    (hlow : ∀ x, x ≠ h → degree C x = 6) (hh : degree C h = 7)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    (univ.filter (fun x : Low h => highDeficit C h x = 0)).card ≤ 14 := by
  apply zero_card_le_fourteen _ (low_card hv h)
  · intro x
    have hr := low_row_identity hv hu hlow x
    have he : 0 ≤ ∑ y, lowExcess C h x y :=
      sum_nonneg (fun y _ => lowExcess_nonneg hpair x y)
    linarith
  · exact high_deficit_sum hv hu hh

/-- The positive-semidefinite remainder in the actual Gram decomposition. -/
theorem three_ones_posSemidef {ι : Type*} [Fintype ι] :
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

/-- In the absence of saturated pairs, the actual low-point Gram matrix
has rank at least twelve. PSD addition is used through its kernel inclusion. -/
theorem low_gram_rank_ge_twelve {C : Family α} {h : α}
    (hv : Fintype.card α = 20) (hu : Uniform C 11)
    (hlow : ∀ x, x ≠ h → degree C x = 6) (hh : degree C h = 7)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    12 ≤ (lowIncidence C h * (lowIncidence C h).transpose).rank := by
  classical
  let G := lowIncidence C h * (lowIncidence C h).transpose
  have hnull := BoundaryRank.two_mul_nullity_le_zero_count 3
    (lowExcess C h) (highDeficit C h) (by norm_num)
    (lowExcess_symm C h) (lowExcess_nonneg hpair) (lowExcess_diagonal C h)
    (highDeficit_nonneg hpair) (low_row_identity hv hu hlow)
  have hzero := highDeficit_zero_card_le hv hu hlow hh hpair
  have hpsd := BoundaryRank.signless_posSemidef (fun _ => 3) (highDeficit C h)
    (lowExcess C h) (lowExcess_symm C h) (lowExcess_nonneg hpair)
    (highDeficit_nonneg hpair) (low_row_identity hv hu hlow)
  have hker := BoundaryRank.ker_add_le_of_posSemidef hpsd
    (three_ones_posSemidef (ι := Low h))
  rw [← low_gram hlow] at hker
  have hdim := Submodule.finrank_mono hker
  have hgker : Module.finrank ℝ (LinearMap.ker G.mulVecLin) ≤ 7 := by
    change Module.finrank ℝ (LinearMap.ker G.mulVecLin) ≤ _ at hdim
    omega
  have htotal := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
  have htotal' : G.rank + Module.finrank ℝ (LinearMap.ker G.mulVecLin) = 19 := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card, low_card hv h]
      using htotal
  change 12 ≤ G.rank
  omega

/-- Every eleven-block covering has a pair of multiplicity exactly two. -/
theorem exists_saturated_pair {C : Family α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3) (hb : C.card = 11) :
    ∃ p q : α, p ≠ q ∧ degree (star C p) q = 2 := by
  classical
  by_contra hno
  have hpair : ∀ x y : α, x ≠ y → 3 ≤ degree (star C x) y := by
    intro x y hxy
    have htwo := pair_ge_two hv hC hxy
    have hne : degree (star C x) y ≠ 2 := fun he => hno ⟨x, y, hxy, he⟩
    omega
  obtain ⟨h, hh, hlow⟩ := degree_profile hv hC hb
  have hl := low_gram_rank_ge_twelve hv hC.1 hlow hh hpair
  have hu : (lowIncidence C h * (lowIncidence C h).transpose).rank ≤ 11 := by
    have hh := (Matrix.rank_mul_le_left (lowIncidence C h)
      (lowIncidence C h).transpose).trans (lowIncidence C h).rank_le_card_width
    simpa only [Fintype.card_coe, hb] using hh
  omega

end CoveringDesigns.C20_11_3
