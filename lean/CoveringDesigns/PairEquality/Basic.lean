import CoveringDesigns.TruncatedPlaneLoads.Incidence
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FieldSimp

/-! Positive unit loads on actual finite supports. Coordinates are never quotiented. -/

namespace CoveringDesigns.PairEquality
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The real incidence vector of an actual support. -/
def indicator (E : Finset I) : I → ℝ := fun x => if x ∈ E then 1 else 0

theorem indicator_injective : Function.Injective (indicator (I := I)) := by
  intro E F h
  ext x
  have hx := congrFun h x
  by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> simp_all [indicator]

@[simp] theorem indicator_sum (E : Finset I) : ∑ x, indicator E x = E.card := by
  simp [indicator, ← sum_filter]

/-- Equal subsets are identified; equal-support actual points are represented by
weights. No independence, regularity or geometric premise is included. -/
structure PositiveUnitLoads (q : ℕ) (H : Finset (Finset I))
    (w : Finset I → ℝ) : Prop where
  coordinates : Fintype.card I = q * (q+1)
  uniform : ∀ E ∈ H, E.card = q+1
  intersect : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).Nonempty
  positive : ∀ E ∈ H, 0 < w E
  load : ∀ x, (∑ E ∈ H, if x ∈ E then w E else 0) = 1

/-- Degree and codegree always count actual members of the specified family. -/
def degree (H : Finset (Finset I)) (x : I) : ℕ := (H.filter (x ∈ ·)).card
def codegree (H : Finset (Finset I)) (x y : I) : ℕ :=
  (H.filter (fun E => x ∈ E ∧ y ∈ E)).card

theorem degree_sum (H : Finset (Finset I)) :
    ∑ x, degree H x = ∑ E ∈ H, E.card := by
  simp only [degree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp

namespace PositiveUnitLoads
variable {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ}
variable (h : PositiveUnitLoads q H w)
include h

theorem meets {E F : Finset I} (hE : E ∈ H) (hF : F ∈ H) :
    (E ∩ F).Nonempty := by
  by_cases he : E = F
  · subst F
    simpa using (card_pos.mp (by rw [h.uniform E hE]; omega) : E.Nonempty)
  · exact h.intersect E hE F hF he

theorem total_weight : (∑ E ∈ H, w E) = q := by
  have he : (∑ x : I, ∑ E ∈ H, if x ∈ E then w E else 0) =
      (q+1 : ℝ) * ∑ E ∈ H, w E := by
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro E hE
    rw [← sum_filter]
    simp [h.uniform E hE]
  simp_rw [h.load] at he
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, h.coordinates,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one] at he
  have hp : (0 : ℝ) < q+1 := by positivity
  nlinarith

private theorem edge_mass {E : Finset I} (hE : E ∈ H) :
    (∑ F ∈ H, w F * ((E ∩ F).card : ℝ)) = q+1 := by
  have he := congrArg (fun f : I → ℝ => ∑ x ∈ E, f x) (funext h.load)
  rw [sum_comm] at he
  have term (F : Finset I) : (∑ x ∈ E, if x ∈ F then w F else 0) =
      w F * ((E ∩ F).card : ℝ) := by
    rw [← sum_filter]
    simp [filter_mem_eq_inter, mul_comm]
  simp_rw [term] at he
  simpa [h.uniform E hE] using he

private theorem edge_term {E F : Finset I} (hE : E ∈ H) (hF : F ∈ H) :
    w F + (if F = E then (q : ℝ) * w E else 0) ≤
      w F * ((E ∩ F).card : ℝ) := by
  by_cases hf : F = E
  · subst F
    simp [h.uniform E hE]
    ring_nf
    exact le_rfl
  · simp only [if_neg hf, add_zero]
    have hc : (1 : ℝ) ≤ (E ∩ F).card := by
      exact_mod_cast card_pos.mpr (h.meets hE hF)
    nlinarith [h.positive F hF]

theorem weight_bound {E : Finset I} (hE : E ∈ H) : (q : ℝ) * w E ≤ 1 := by
  have he := sum_le_sum (fun F hF => h.edge_term hE hF)
  rw [sum_add_distrib, h.total_weight, sum_ite_eq', if_pos hE, h.edge_mass hE] at he
  linarith

theorem degree_lower (x : I) : q ≤ degree H x := by
  have hs : (∑ E ∈ H.filter (x ∈ ·), (q : ℝ) * w E) = q := by
    rw [← mul_sum, sum_filter, h.load, mul_one]
  have he := sum_le_sum (fun E (hE : E ∈ H.filter (x ∈ ·)) =>
    h.weight_bound (mem_filter.mp hE).1)
  rw [hs] at he
  simpa [degree] using he

theorem card_lower : q*q ≤ H.card := by
  have he := sum_le_sum (fun E hE => h.weight_bound hE)
  rw [← mul_sum, h.total_weight] at he
  exact_mod_cast (by simpa using he : (q : ℝ)*q ≤ H.card)

/-- A minimum-degree coordinate saturates each of its incident weights. -/
theorem saturated_of_degree {x : I} (hx : degree H x = q)
    {E : Finset I} (hE : E ∈ H) (hxe : x ∈ E) : (q : ℝ) * w E = 1 := by
  have hs : (∑ F ∈ H.filter (x ∈ ·), (q : ℝ) * w F) =
      ∑ _F ∈ H.filter (x ∈ ·), (1 : ℝ) := by
    rw [← mul_sum, sum_filter, h.load, mul_one]
    simpa [degree] using congrArg (fun n : ℕ => (n : ℝ)) hx.symm
  exact (sum_eq_sum_iff_of_le (fun F hF => h.weight_bound (mem_filter.mp hF).1)).mp hs
    E (mem_filter.mpr ⟨hE,hxe⟩)

/-- Saturated supports meet every other occupied support exactly once. -/
theorem saturated_intersection {E : Finset I} (hE : E ∈ H)
    (hw : (q : ℝ) * w E = 1) {F : Finset I} (hF : F ∈ H) (hEF : E ≠ F) :
    (E ∩ F).card = 1 := by
  have hs : (∑ R ∈ H, (w R + (if R = E then (q : ℝ) * w E else 0))) =
      ∑ R ∈ H, w R * ((E ∩ R).card : ℝ) := by
    rw [sum_add_distrib, h.total_weight, sum_ite_eq', if_pos hE, hw, h.edge_mass hE]
  have he := (sum_eq_sum_iff_of_le (fun R hR => h.edge_term hE hR)).mp hs F hF
  rw [if_neg (Ne.symm hEF), add_zero] at he
  have hc : ((E ∩ F).card : ℝ) = 1 := by nlinarith [h.positive F hF]
  exact_mod_cast hc

end PositiveUnitLoads
end CoveringDesigns.PairEquality
