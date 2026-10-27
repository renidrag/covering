import CoveringDesigns.TruncatedPlaneLoads.Incidence
import Mathlib.Data.Finset.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Matrix.Basic

/-! Completion of the actual truncated core, retaining coordinates and supports. -/

open Finset Matrix
open scoped BigOperators

namespace CoveringDesigns.C6k_K_2

variable {I : Type*} [Fintype I] [DecidableEq I]
  (P : TruncatedPlaneLoads.Plane 6 I (Fin 7))

include P

/-- Core supports stay on the original coordinates; each group gains the new point. -/
def completedLine : P.core ⊕ Fin 7 → Finset (Option I)
  | Sum.inl E => E.val.map Function.Embedding.some
  | Sum.inr g => insert none ((P.groupSet g).map Function.Embedding.some)

theorem completed_points_card : Fintype.card (Option I) = 43 := by
  simp [Fintype.card_option, P.coordinates_card]

theorem completed_lines_card : Fintype.card (P.core ⊕ Fin 7) = 43 := by
  simp [P.core_card]

theorem completed_line_size (l : P.core ⊕ Fin 7) : (completedLine P l).card = 7 := by
  cases l with
  | inl E => simpa [completedLine] using P.core_size E.property
  | inr g => simp [completedLine]

private theorem core_group_intersection (E : P.core) (g : Fin 7) :
    ((completedLine P (Sum.inl E)) ∩ (completedLine P (Sum.inr g))).card = 1 := by
  have he : completedLine P (Sum.inl E) ∩ completedLine P (Sum.inr g) =
      (E.val.filter (P.group · = g)).map Function.Embedding.some := by
    ext x
    cases x <;> simp [completedLine]
  rw [he, card_map, P.transversal E E.property]

theorem completed_intersection (l m : P.core ⊕ Fin 7) (hne : l ≠ m) :
    (completedLine P l ∩ completedLine P m).card = 1 := by
  cases l with
  | inl E =>
    cases m with
    | inl F =>
      change (E.val.map Function.Embedding.some ∩ F.val.map Function.Embedding.some).card = 1
      rw [← map_inter, card_map]
      exact P.intersection E E.property F F.property
        (fun h => hne (congrArg Sum.inl (Subtype.ext h)))
    | inr g => exact core_group_intersection P E g
  | inr g =>
    cases m with
    | inl E => rw [inter_comm]; exact core_group_intersection P E g
    | inr h =>
      have hgh : g ≠ h := fun he => hne (congrArg Sum.inr he)
      have he : completedLine P (Sum.inr g) ∩ completedLine P (Sum.inr h) = {none} := by
        ext x
        cases x with
        | none => simp [completedLine]
        | some x =>
          simp only [completedLine, mem_inter, mem_insert, Option.some_ne_none, false_or,
            mem_map, Function.Embedding.some_apply, Option.some.injEq, exists_eq_right,
            TruncatedPlaneLoads.Plane.mem_groupSet, mem_singleton, Option.some_ne_none]
          exact ⟨fun hx => hgh (hx.1.symm.trans hx.2), False.elim⟩
      rw [he, card_singleton]

theorem completed_lines_injective : Function.Injective (completedLine P) := by
  intro l m he
  by_contra hne
  have h := completed_intersection P l m hne
  rw [he, inter_self, completed_line_size] at h
  omega

private theorem point_count (x y : Option I) :
    (∑ l : P.core ⊕ Fin 7, if x ∈ completedLine P l ∧ y ∈ completedLine P l
      then (1 : ℕ) else 0) = if x = y then 7 else 1 := by
  rw [Fintype.sum_sum_type]
  cases x with
  | none => cases y <;> simp [completedLine, eq_comm]
  | some x =>
    cases y with
    | none => simp [completedLine, eq_comm]
    | some y =>
      simp only [completedLine, mem_map, Function.Embedding.some_apply, Option.some.injEq,
        exists_eq_right, mem_insert, Option.some_ne_none, false_or,
        TruncatedPlaneLoads.Plane.mem_groupSet]
      rw [sum_coe_sort P.core (fun E => if x ∈ E ∧ y ∈ E then (1 : ℕ) else 0)]
      rw [← sum_filter, ← card_eq_sum_ones]
      have hg : (∑ g : Fin 7, if P.group x = g ∧ P.group y = g then (1 : ℕ) else 0) =
          if P.group x = P.group y then 1 else 0 := by
        simp [ite_and, eq_comm]
      rw [hg]
      by_cases hxy : x = y
      · subst y
        simpa using P.degree x
      · rw [P.codegree x y hxy]
        split_ifs <;> simp_all

theorem completed_degree (x : Option I) :
    (univ.filter (fun l => x ∈ completedLine P l)).card = 7 := by
  simpa only [card_eq_sum_ones, sum_filter, and_self, ite_true, eq_self_iff_true]
    using point_count P x x

theorem completed_codegree (x y : Option I) (hne : x ≠ y) :
    (univ.filter (fun l => x ∈ completedLine P l ∧ y ∈ completedLine P l)).card = 1 := by
  have h := point_count P x y
  rw [if_neg hne] at h
  simpa only [card_eq_sum_ones, sum_filter] using h

/-- Incidence on the actual completed line and point types. -/
def completedIncidence : Matrix (P.core ⊕ Fin 7) (Option I) ℤ :=
  fun l x => if x ∈ completedLine P l then 1 else 0

theorem completed_row_sum (l : P.core ⊕ Fin 7) : ∑ x, completedIncidence P l x = 7 := by
  have hc := completed_line_size P l
  have he : (∑ x, completedIncidence P l x) = ((completedLine P l).card : ℤ) := by
    simp only [completedIncidence]
    rw [← sum_filter]
    have hf : univ.filter (fun x => x ∈ completedLine P l) = completedLine P l := by
      ext x
      simp
    rw [hf]
    simp
  rw [he, hc]
  rfl

theorem completed_row_gram :
    completedIncidence P * (completedIncidence P).transpose =
      (6 : ℤ) • 1 + Matrix.of (fun (_ _ : P.core ⊕ Fin 7) => (1 : ℤ)) := by
  ext l m
  have he : (completedIncidence P * (completedIncidence P).transpose) l m =
      ((completedLine P l ∩ completedLine P m).card : ℤ) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, completedIncidence,
      ite_mul, one_mul, zero_mul, ← ite_and]
    rw [← sum_filter]
    have hf : univ.filter (fun x => x ∈ completedLine P l ∧ x ∈ completedLine P m) =
        completedLine P l ∩ completedLine P m := by
      ext x
      simp
    rw [hf]
    simp
  rw [he]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Matrix.of_apply]
  by_cases h : l = m
  · subst m
    simp [completed_line_size]
  · rw [completed_intersection P l m h]
    simp [h]

theorem completed_column_gram :
    (completedIncidence P).transpose * completedIncidence P =
      (6 : ℤ) • 1 + Matrix.of (fun (_ _ : Option I) => (1 : ℤ)) := by
  ext x y
  have he : ((completedIncidence P).transpose * completedIncidence P) x y =
      ((univ.filter (fun l => x ∈ completedLine P l ∧ y ∈ completedLine P l)).card : ℤ) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, completedIncidence,
      card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply sum_congr rfl
    intro l _
    split_ifs <;> simp_all
  rw [he]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Matrix.of_apply]
  by_cases h : x = y
  · subst y
    simpa using congrArg (fun n : ℕ => (n : ℤ)) (completed_degree P x)
  · rw [completed_codegree P x y h]
    simp [h]

end CoveringDesigns.C6k_K_2
