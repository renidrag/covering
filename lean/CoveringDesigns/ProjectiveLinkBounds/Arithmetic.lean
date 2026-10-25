import CoveringDesigns.Equality.FiniteSum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Zify

/-! Exact arithmetic for the projective-link bounds. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.ProjectiveLinkBounds
open Finset

def pointCount (q : ℕ) : ℕ := q^2 + q + 1
def collinearFloor (q : ℕ) : ℕ := Schoenheim.ceilDiv q 4
def tripleDemand (q : ℕ) : ℕ := pointCount q * q^3 * (q+1) / 6
def capacity (q : ℕ) : ℕ := (q+2).choose 3 - collinearFloor q
def familyBound (q : ℕ) : ℕ :=
  min (Schoenheim.ceilDiv ((pointCount q+1)*(pointCount q+2)) (q+2))
    (pointCount q + Schoenheim.ceilDiv (tripleDemand q) (capacity q))
def weakBound (q : ℕ) : ℕ := Schoenheim.ceilDiv ((pointCount q+1)^2) (q+2)

namespace Internal

theorem choose_two_int (m : ℕ) :
    2 * (m.choose 2 : ℤ) = (m : ℤ) * ((m : ℤ)-1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 2
  norm_num [Nat.descFactorial_succ, Nat.factorial] at h
  by_cases hm : m = 0
  · subst m; norm_num
  · have hs : 1 ≤ m := by omega
    have hh := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub hs] at hh
    nlinarith

theorem choose_three_int (m : ℕ) :
    6 * (m.choose 3 : ℤ) = (m : ℤ) * ((m : ℤ)-1) * ((m : ℤ)-2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 3
  norm_num [Nat.descFactorial_succ, Nat.factorial] at h
  by_cases hm : m < 2
  · interval_cases m <;> norm_num [Nat.choose]
  · have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have hh := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at hh
    nlinarith

theorem floor_bounds {q : ℕ} (ho : Odd q) :
    q+1 ≤ 4*collinearFloor q ∧ 4*collinearFloor q ≤ q+3 := by
  rcases ho with ⟨a,ha⟩
  unfold collinearFloor Schoenheim.ceilDiv
  omega

private theorem floor_le {q : ℕ} (hq : 1 ≤ q) : collinearFloor q ≤ q := by
  exact (Schoenheim.ceilDiv_le_iff (by omega : 0 < 4)).mpr (by omega)

end Internal

theorem collinearFloor_eq {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) :
    Schoenheim.ceilDiv (q^2-1) (4*q-2) = collinearFloor q := by
  have hb := Internal.floor_bounds ho
  have hp : 0 < 4*q-2 := by omega
  have hn : 1 ≤ q^2 := by nlinarith
  have hu : q^2-1 ≤ (4*q-2)*collinearFloor q := by
    have hmul := Nat.mul_le_mul_left (4*q-2) hb.1
    zify [hn, show 2 ≤ 4*q by omega] at *
    nlinarith
  apply Nat.le_antisymm ((Schoenheim.ceilDiv_le_iff hp).mpr hu)
  have hc := (Schoenheim.ceilDiv_le_iff hp).mp
    (le_refl (Schoenheim.ceilDiv (q^2-1) (4*q-2)))
  by_contra hh
  have hmul := Nat.mul_le_mul_left (4*q-2)
    (show 4*Schoenheim.ceilDiv (q^2-1) (4*q-2) ≤ q-1 by omega)
  zify [hn, show 2 ≤ 4*q by omega, show 1 ≤ q by omega] at *
  nlinarith

theorem capacity_ge {q : ℕ} (hq : 3 ≤ q) :
    (q+1).choose 3 ≤ capacity q := by
  have hf := Internal.floor_le (show 1 ≤ q by omega)
  have hc := Internal.choose_two_int (q+1)
  have hq : q ≤ (q+1).choose 2 := by
    push_cast at hc
    have hq' : (1 : ℤ) ≤ q := by omega
    have hh : (q : ℤ) ≤ (q+1).choose 2 := by nlinarith
    exact_mod_cast hh
  have he : (q+2).choose 3 = (q+1).choose 2 + (q+1).choose 3 := by
    simpa [Nat.add_assoc] using Nat.choose_succ_succ (q+1) 2
  unfold capacity
  omega

theorem capacity_pos {q : ℕ} (hq : 3 ≤ q) : 0 < capacity q :=
  lt_of_lt_of_le (Nat.choose_pos (by omega)) (capacity_ge hq)

theorem capacity_balance {q : ℕ} (hq : 3 ≤ q) :
    capacity q + collinearFloor q = (q+2).choose 3 := by
  exact Nat.sub_add_cancel (Nat.sub_pos_iff_lt.mp (capacity_pos hq)).le

theorem demand_balance (q : ℕ) :
    tripleDemand q + pointCount q * (q+1).choose 3 = (pointCount q).choose 3 := by
  have hn := Internal.choose_three_int (pointCount q)
  have hk := Internal.choose_three_int (q+1)
  have hm := congrArg (fun z : ℤ => (pointCount q : ℤ)*z) hk
  have he : 6*(pointCount q).choose 3 =
      6*(pointCount q*(q+1).choose 3)+pointCount q*q^3*(q+1) := by
    zify
    unfold pointCount at hn hm ⊢
    push_cast at hn hm ⊢
    nlinarith
  unfold tripleDemand
  omega

theorem demand_six (q : ℕ) :
    6*tripleDemand q = pointCount q*q^3*(q+1) := by
  have h := demand_balance q
  have hn := Internal.choose_three_int (pointCount q)
  have hk := Internal.choose_three_int (q+1)
  have hm := congrArg (fun z : ℤ => (pointCount q : ℤ)*z) hk
  zify at h ⊢
  unfold pointCount at hn hm h ⊢
  push_cast at hn hm h ⊢
  nlinarith

/-- The completion branch is always the smaller rounded bound. -/
theorem familyBound_eq_completion {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) :
    familyBound q = pointCount q + Schoenheim.ceilDiv (tripleDemand q) (capacity q) := by
  have hf : 3 * collinearFloor q ≤ q+1 := by
    by_cases he : q = 3
    · subst q; norm_num [collinearFloor, Schoenheim.ceilDiv]
    · have hb := Internal.floor_bounds ho
      obtain ⟨a, ha⟩ := ho
      omega
  have hcross : (q+2) * (pointCount q * capacity q + tripleDemand q) ≤
      capacity q * (pointCount q+1) * (pointCount q+2) := by
    have hN := demand_six q
    have hM := capacity_balance hq
    have hC := Internal.choose_three_int (q+2)
    zify at hN hM hf ⊢
    push_cast at hC
    let D : ℤ := (pointCount q : ℤ) * (q : ℤ)^2 + 2*pointCount q + 2
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hq' : (3 : ℤ) ≤ q := by omega
    have hgap : D < (q : ℤ) * ((q : ℤ)+2) * ((pointCount q : ℤ)+1) := by
      have hp := mul_nonneg (show (0 : ℤ) ≤ pointCount q by positivity)
        (show (0 : ℤ) ≤ q-1 by omega)
      dsimp [D]
      nlinarith [sq_nonneg (q : ℤ)]
    have hw := mul_le_mul_of_nonneg_right hf hD
    have hs := mul_lt_mul_of_pos_left hgap (show (0 : ℤ) < q+1 by omega)
    have hC' := congrArg (fun z : ℤ => z*((pointCount q : ℤ)+1)) hC
    have hh : (collinearFloor q : ℤ)*D <
        2*((q+2).choose 3 : ℤ)*((pointCount q : ℤ)+1) := by
      nlinarith only [hw, hs, hC']
    have hNC : ((q : ℤ)+2)*tripleDemand q =
        ((q+2).choose 3 : ℤ)*pointCount q*(q : ℤ)^2 := by
      have hN' := congrArg (fun z : ℤ => ((q : ℤ)+2)*z) hN
      have hC'' := congrArg (fun z : ℤ => (pointCount q : ℤ)*(q : ℤ)^2*z) hC
      nlinarith only [hN', hC'']
    have hM' := congrArg (fun z : ℤ => z*D) hM
    have hid : (capacity q : ℤ)*((pointCount q : ℤ)+1)*((pointCount q : ℤ)+2) -
        ((q : ℤ)+2)*((pointCount q : ℤ)*capacity q+tripleDemand q) =
        2*((q+2).choose 3 : ℤ)*((pointCount q : ℤ)+1)-(collinearFloor q : ℤ)*D := by
      dsimp [D] at hM' ⊢
      unfold pointCount at hM' hNC ⊢
      push_cast at hM' hNC ⊢
      nlinarith only [hM', hNC]
    nlinarith only [hid, hh]
  let z := Schoenheim.ceilDiv ((pointCount q+1)*(pointCount q+2)) (q+2)
  have hz : (pointCount q+1)*(pointCount q+2) ≤ (q+2)*z :=
    (Schoenheim.ceilDiv_le_iff (by omega)).mp (le_refl z)
  have hm := Nat.mul_le_mul_left (capacity q) hz
  have hs : pointCount q * capacity q + tripleDemand q ≤ capacity q * z := by
    nlinarith only [hcross, hm, show 0 < q+2 by omega]
  have hn : pointCount q ≤ z := by
    have hp := capacity_pos hq
    nlinarith only [hs, hp]
  have ht : tripleDemand q ≤ capacity q * (z-pointCount q) := by
    zify [hn] at hs ⊢
    nlinarith only [hs]
  have hc := (Schoenheim.ceilDiv_le_iff (capacity_pos hq)).mpr ht
  apply min_eq_right
  change pointCount q + Schoenheim.ceilDiv (tripleDemand q) (capacity q) ≤ z
  omega

end CoveringDesigns.ProjectiveLinkBounds
