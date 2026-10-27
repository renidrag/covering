import CoveringDesigns.PairEquality.Basic
import Mathlib.Analysis.Convex.Caratheodory

/-! Support-preserving Carathéodory extraction; the auxiliary weights may change. -/

namespace CoveringDesigns.PairEquality
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A feasible subfamily on the original coordinates with independent incidence
columns. Its coefficients need not agree with the original coefficients. -/
theorem independent_subfamily {q : ℕ} (hq : 0 < q)
    {H : Finset (Finset I)} {w : Finset I → ℝ} (h : PositiveUnitLoads q H w) :
    ∃ J ⊆ H, ∃ a : Finset I → ℝ, PositiveUnitLoads q J a ∧
      LinearIndependent ℝ (fun E : J => indicator E.val) ∧ J.card ≤ Fintype.card I := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let u : I → ℝ := fun _ => 1 / q
  have hw : (∑ E ∈ H, w E / q) = 1 := by
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul, h.total_weight, mul_inv_cancel₀ (ne_of_gt hqR)]
  have hu : (∑ E ∈ H, (w E / q) • indicator E) = u := by
    ext x
    simp only [sum_apply, Pi.smul_apply, smul_eq_mul, indicator]
    have term (E : Finset I) : w E / q * (if x ∈ E then 1 else 0) =
        (if x ∈ E then w E else 0) / q := by split_ifs <;> simp
    simp_rw [term]
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul, h.load]
    rfl
  have hx : u ∈ convexHull ℝ (indicator '' (H : Set (Finset I))) := by
    have he := H.centerMass_mem_convexHull (s := indicator '' (H : Set (Finset I)))
      (z := indicator)
      (fun E hE => div_nonneg (h.positive E hE).le hqR.le)
      (by rw [hw]; norm_num : 0 < ∑ E ∈ H, w E / q)
      (fun E hE => ⟨E,hE,rfl⟩ : ∀ E ∈ H, indicator E ∈ indicator '' (H : Set (Finset I)))
    rw [centerMass_eq_of_sum_1 _ _ hw, hu] at he
    exact he
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ht : (t : Set (I → ℝ)) ⊆ indicator '' (H : Set (Finset I)) :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hi : AffineIndependent ℝ ((↑) : t → (I → ℝ)) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  obtain ⟨b,hb,hs,hv⟩ := Finset.mem_convexHull'.mp
    (Caratheodory.mem_minCardFinsetOfMemConvexHull hx)
  let J := H.filter (fun E => indicator E ∈ t ∧ b (indicator E) ≠ 0)
  have hj : J ⊆ H := filter_subset _ _
  have himage : J.image indicator = t.filter (fun v => b v ≠ 0) := by
    ext v
    constructor
    · rintro hv'
      obtain ⟨E,hE,rfl⟩ := mem_image.mp hv'
      exact mem_filter.mpr (mem_filter.mp hE).2
    · intro hv'
      obtain ⟨E,hE,rfl⟩ := ht (mem_filter.mp hv').1
      exact mem_image.mpr ⟨E,mem_filter.mpr ⟨hE,mem_filter.mp hv'⟩,rfl⟩
  have hsum : (∑ E ∈ J, b (indicator E) • indicator E) = u := by
    rw [← sum_image (f := fun v : I → ℝ => b v • v)
      (fun E _ F _ he => indicator_injective he), himage]
    rw [sum_filter_of_ne]
    · exact hv
    · intro v _ hne he
      exact hne (by rw [he, zero_smul])
  let a := fun E : Finset I => (q : ℝ) * b (indicator E)
  have ha : PositiveUnitLoads q J a := {
    coordinates := h.coordinates
    uniform := fun E hE => h.uniform E (hj hE)
    intersect := fun E hE F hF => h.intersect E (hj hE) F (hj hF)
    positive := by
      intro E hE
      have he := (mem_filter.mp hE).2
      exact mul_pos hqR (lt_of_le_of_ne (hb _ he.1) (Ne.symm he.2))
    load := by
      intro x
      have he := congrFun hsum x
      simp only [sum_apply, Pi.smul_apply, smul_eq_mul, indicator, u] at he
      have term (E : Finset I) : (if x ∈ E then a E else 0) =
          (q : ℝ) * (b (indicator E) * (if x ∈ E then 1 else 0)) := by
        split_ifs <;> simp [a]
      simp_rw [term]
      rw [← mul_sum, he, mul_one_div_cancel (ne_of_gt hqR)] }
  let f : J ↪ t := {
    toFun := fun E => ⟨indicator E.val,(mem_filter.mp E.property).2.1⟩
    inj' := by
      intro E F he
      exact Subtype.ext (indicator_injective (congrArg Subtype.val he)) }
  have hai : AffineIndependent ℝ (fun E : J => indicator E.val) := hi.comp_embedding f
  have hli : LinearIndependent ℝ (fun E : J => indicator E.val) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc E
    have hz := congrArg (fun v : I → ℝ => ∑ x, v x) hc
    simp only [sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sum_const_zero] at hz
    rw [sum_comm] at hz
    simp_rw [← mul_sum, indicator_sum, ha.uniform _ (Subtype.mem _), Nat.cast_add,
      Nat.cast_one] at hz
    rw [← sum_mul] at hz
    have hcz : (∑ F : J, c F) = 0 := by
      exact (mul_eq_zero.mp hz).resolve_right (by positivity)
    exact hai.eq_zero_of_sum_eq_zero hcz hc E (mem_univ _)
  refine ⟨J,hj,a,ha,hli,?_⟩
  simpa using hli.fintype_card_le_finrank

end CoveringDesigns.PairEquality
