import CoveringDesigns.PairEquality.Compatibility
import CoveringDesigns.TruncatedPlaneLoads.Examples

/-! The unchanged pure-core and positive-extra-support controls, at unit load. -/

namespace CoveringDesigns.PairEquality.Examples
open Finset TruncatedPlaneLoads TruncatedPlaneLoads.Examples

private theorem normalize {I G : Type*} [Fintype I] [DecidableEq I]
    [Fintype G] [DecidableEq G] {q : ℕ} {P : Plane q I G}
    {H : Finset (Finset I)} {w : Finset I → ℝ} {K : ℝ} (h : Admissible P H w K) :
    PositiveUnitLoads q H (fun E => w E / K) := by
  refine ⟨P.coordinates_card,h.uniform,fun _ hE _ hF _ => h.intersect _ hE _ hF,
    fun E hE => div_pos (h.positive E hE) h.load_pos,?_⟩
  intro x
  have ht (E : Finset I) : (if x ∈ E then w E / K else 0) =
      (if x ∈ E then w E else 0) * K⁻¹ := by split_ifs <;> simp [div_eq_mul_inv]
  simp_rw [ht]
  rw [← sum_mul,h.load,mul_inv_cancel₀ (ne_of_gt h.load_pos)]

noncomputable def pureWeight : Finset (Fin 20) → ℝ := fun _ => 1/4
noncomputable def extendedWeight (E : Finset (Fin 20)) : ℝ := (multiplicity4 E : ℝ)/8

theorem pure_unit_loads : PositiveUnitLoads 4 plane4.core pureWeight := by
  unfold pureWeight
  convert normalize pure4.toReal using 1 <;> norm_num

theorem extended_unit_loads : PositiveUnitLoads 4 (plane4.extension 0) extendedWeight := by
  unfold extendedWeight
  convert normalize extended4.toReal using 1 <;> norm_num

theorem pure_core_branch : ∃ P : Plane 4 (Fin 20) (Fin 5),
    Admissible P plane4.core pureWeight 1 := by
  apply (admissible_or_twisted (by decide) pure_unit_loads).resolve_right
  intro h
  have hc := h.supports
  have he : plane4.core.card = 16 := plane4.core_card
  omega

/-- Uniform weighted loads do not imply uniform unweighted degrees. -/
theorem extended_degrees : degree (plane4.extension 0) 0 = 8 ∧
    degree (plane4.extension 0) 1 = 4 ∧ degree (plane4.extension 0) 4 = 5 := by decide

/-- This conclusion is obtained from the dichotomy; no selected or unique
auxiliary core is prescribed. All original occupied supports are retained. -/
theorem extended_core_branch : ∃ P : Plane 4 (Fin 20) (Fin 5),
    Admissible P (plane4.extension 0) extendedWeight 1 := by
  apply (admissible_or_twisted (by decide) extended_unit_loads).resolve_right
  intro h
  have hd := h.degree_eq 0
  have he := extended_degrees.1
  omega

theorem positive_extra_retained : plane4.extra 1 0 ∈ plane4.extension 0 ∧
    plane4.extra 1 0 ∉ plane4.core ∧ extendedWeight (plane4.extra 1 0) = 1/8 := by
  refine ⟨two_coordinate_intersection.1,plane4.extra_not_core (by decide),?_⟩
  have he : multiplicity4 (plane4.extra 1 0) = 1 := by decide
  simp [extendedWeight,he]

theorem double_intersection_allowed :
    coreEdge 0 ∈ plane4.extension 0 ∧ plane4.extra 1 0 ∈ plane4.extension 0 ∧
    (plane4.extra 1 0 ∩ coreEdge 0).card = 2 :=
  ⟨extended4.core_subset two_coordinate_intersection.2.1,
    two_coordinate_intersection.1,two_coordinate_intersection.2.2⟩

end CoveringDesigns.PairEquality.Examples
