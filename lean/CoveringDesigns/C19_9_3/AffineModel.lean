import CoveringDesigns.C19_9_3.Orthogonality
import CoveringDesigns.Equality.FiniteSum

/-! The fixed eight-point affine model and universal column identities.
Actual recognition and transport are separate obligations. -/
namespace CoveringDesigns.C19_9_3
open Finset

abbrev PlanePosition := Fin 7 × Bool

def orientation (n : Fin 7) (x : Fin 8) : Bool := character n x == -1

def affinePlane (p : PlanePosition) : Finset (Fin 8) :=
  univ.filter fun x => orientation p.1 x = p.2

def affinePointSupport (x : Fin 8) : Finset PlanePosition :=
  univ.filter fun p => x ∈ affinePlane p

section FixedPlanes
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem affine_plane_card : ∀ p, (affinePlane p).card = 4 := by
  rintro ⟨n,b⟩
  cases b <;> revert n <;> decide +kernel

theorem affine_point_degree : ∀ x, (affinePointSupport x).card = 7 := by decide +kernel

theorem affine_pair_degree : ∀ x y : Fin 8, x ≠ y →
    (affinePointSupport x ∩ affinePointSupport y).card = 3 := by
  decide +kernel

theorem affine_triple_degree : ∀ x y z : Fin 8, x ≠ y → x ≠ z → y ≠ z →
    (affinePointSupport x ∩ affinePointSupport y ∩ affinePointSupport z).card = 1 := by
  decide +kernel

theorem affine_root_line : ∀ x y : Fin 8, x ≠ y →
    ∃ l, (univ.filter fun n : Fin 7 => orientation n x = orientation n y) = SevenBlock.line l := by
  decide +kernel

theorem affine_root_all_lines : ∀ x : Fin 8, ∀ l,
    ∃ y : Fin 8, x ≠ y ∧
      (univ.filter fun n : Fin 7 => orientation n x = orientation n y) = SevenBlock.line l := by
  decide +kernel

end FixedPlanes

def columnDirections (U : Finset PlanePosition) (x : Fin 8) : Finset (Fin 7) :=
  univ.filter fun n => (n,orientation n x) ∈ U

def columnValue (U : Finset PlanePosition) (x : Fin 8) : ℕ := (columnDirections U x).card

def columnCoefficient (U : Finset PlanePosition) (n : Fin 7) : ℤ :=
  (if (n,false) ∈ U then 1 else 0) - (if (n,true) ∈ U then 1 else 0)

private theorem plane_card_sum (U : Finset PlanePosition) :
    U.card = ∑ n : Fin 7, ((if (n,false) ∈ U then 1 else 0) + (if (n,true) ∈ U then 1 else 0)) := by
  have hc : U.card = ∑ p : PlanePosition, if p ∈ U then 1 else 0 := by simp
  rw [hc,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  apply sum_congr rfl
  intro n _
  omega

/-- Fourier expansion for an arbitrary selected set of actual plane
positions. There is no enumeration of column subsets. -/
theorem column_character_identity (U : Finset PlanePosition) (x : Fin 8) :
    2 * (columnValue U x : ℤ) - U.card =
      ∑ n : Fin 7, columnCoefficient U n * character n x := by
  have hc : (columnValue U x : ℤ) =
      ∑ n : Fin 7, if (n,orientation n x) ∈ U then (1 : ℤ) else 0 := by
    simp only [columnValue,columnDirections,card_eq_sum_ones,sum_filter,Nat.cast_sum,
      Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hN : (U.card : ℤ) = ∑ n : Fin 7,
      ((if (n,false) ∈ U then (1 : ℤ) else 0) + (if (n,true) ∈ U then 1 else 0)) := by
    exact_mod_cast plane_card_sum U
  rw [hc,hN,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  rcases character_sign n x with hn | hn <;>
    by_cases h0 : (n,false) ∈ U <;> by_cases h1 : (n,true) ∈ U <;>
    simp [columnCoefficient,orientation,hn,h0,h1]

/-- Every selected plane contributes four incidences. -/
theorem column_incidence_sum (U : Finset PlanePosition) :
    ∑ x : Fin 8, columnValue U x = 4 * U.card := by
  have hterm (n : Fin 7) : (∑ x : Fin 8, if (n,orientation n x) ∈ U then 1 else 0) =
      4 * ((if (n,false) ∈ U then 1 else 0) + (if (n,true) ∈ U then 1 else 0)) := by
    have hf := affine_plane_card (n,false)
    have ht := affine_plane_card (n,true)
    have hor : ∀ x, orientation n x = false ∨ orientation n x = true := fun x =>
      (Bool.eq_false_or_eq_true _).symm
    have hsplit (x : Fin 8) : (if (n,orientation n x) ∈ U then 1 else 0) =
        (if (n,false) ∈ U then (if orientation n x = false then 1 else 0) else 0) +
        (if (n,true) ∈ U then (if orientation n x = true then 1 else 0) else 0) := by
      rcases hor x with hx | hx <;> simp [hx]
    simp only [affinePlane,card_eq_sum_ones,sum_filter] at hf ht
    simp_rw [hsplit]
    rw [sum_add_distrib]
    by_cases h0 : (n,false) ∈ U <;> by_cases h1 : (n,true) ∈ U <;> simp [h0,h1,hf,ht]
  simp only [columnValue,columnDirections,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  simp_rw [hterm]
  rw [← mul_sum,← plane_card_sum]
  simp

#guard_standard_axioms affine_plane_card affine_point_degree affine_pair_degree
  affine_triple_degree affine_root_line affine_root_all_lines
  column_character_identity column_incidence_sum

end CoveringDesigns.C19_9_3
