import CoveringDesigns.Foundations.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Finite incidence data for a truncated projective plane. No field is required. -/

namespace CoveringDesigns.TruncatedPlaneLoads

open Finset
variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]

/-- Coordinates partition into parallel classes; core supports are point pencils
in the dual affine plane. All fields are ordinary finite incidence axioms. -/
structure Plane (q : ℕ) (V G : Type*) [Fintype V] [DecidableEq V]
    [Fintype G] [DecidableEq G] where
  group : V → G
  core : Finset (Finset V)
  groups_card : Fintype.card G = q + 1
  group_card : ∀ i, (univ.filter (group · = i)).card = q
  transversal : ∀ E ∈ core, ∀ i, (E.filter (group · = i)).card = 1
  degree : ∀ x, (core.filter (x ∈ ·)).card = q
  codegree : ∀ x y, x ≠ y →
    (core.filter (fun E => x ∈ E ∧ y ∈ E)).card = if group x = group y then 0 else 1
  intersection : ∀ E ∈ core, ∀ F ∈ core, E ≠ F → (E ∩ F).card = 1

variable {q : ℕ} (P : Plane q V G)

namespace Plane
include P

def groupSet (i : G) : Finset V := univ.filter (P.group · = i)

@[simp] theorem mem_groupSet (i : G) (x : V) : x ∈ P.groupSet i ↔ P.group x = i := by
  simp [groupSet]

@[simp] theorem groupSet_card (i : G) : (P.groupSet i).card = q := P.group_card i

theorem coordinates_card : Fintype.card V = q * (q+1) := by
  have h : (∑ i : G, (univ.filter (P.group · = i)).card) = Fintype.card V := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    simp
  simpa [P.group_card, P.groups_card, Nat.mul_comm] using h.symm

theorem core_size {E : Finset V} (hE : E ∈ P.core) : E.card = q+1 := by
  have h : (∑ i : G, (E.filter (P.group · = i)).card) = E.card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    simp
  simpa [P.transversal E hE, P.groups_card] using h.symm

theorem core_card : P.core.card = q*q := by
  have hG : Nonempty G := Fintype.card_pos_iff.mp (by rw [P.groups_card]; omega)
  obtain ⟨i⟩ := hG
  have h : (∑ x ∈ P.groupSet i, (P.core.filter (x ∈ ·)).card) = P.core.card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    have he (E : Finset V) (hE : E ∈ P.core) :
        (∑ x ∈ P.groupSet i, if x ∈ E then 1 else 0) = 1 := by
      have eq : (P.groupSet i).filter (· ∈ E) = E.filter (P.group · = i) := by
        ext x
        simp [and_comm]
      rw [← sum_filter, ← card_eq_sum_ones, eq, P.transversal E hE i]
    rw [sum_congr rfl he]
  simpa [P.degree] using h.symm

theorem same_group {E : Finset V} (hE : E ∈ P.core)
    {x y : V} (hx : x ∈ E) (hy : y ∈ E) (hg : P.group x = P.group y) : x = y := by
  obtain ⟨z, hz⟩ := card_eq_one.mp (P.transversal E hE (P.group x))
  have hx' : x ∈ E.filter (P.group · = P.group x) := by simp [hx]
  have hy' : y ∈ E.filter (P.group · = P.group x) := by simp [hy, hg]
  rw [hz] at hx' hy'
  simpa only [mem_singleton] using (mem_singleton.mp hx').trans (mem_singleton.mp hy').symm

theorem join {x y : V} (hg : P.group x ≠ P.group y) :
    ∃ E ∈ P.core, x ∈ E ∧ y ∈ E := by
  have hxy : x ≠ y := fun h => hg (congrArg P.group h)
  have h := P.codegree x y hxy
  rw [if_neg hg] at h
  obtain ⟨E, hE⟩ := card_pos.mp (by omega : 0 < (P.core.filter (fun E => x ∈ E ∧ y ∈ E)).card)
  exact ⟨E, (mem_filter.mp hE).1, (mem_filter.mp hE).2⟩

theorem core_avoiding (hq : 2 ≤ q) (c : V) : ∃ E ∈ P.core, c ∉ E := by
  by_contra h
  push_neg at h
  have eq : P.core.filter (c ∈ ·) = P.core := filter_eq_self.mpr h
  have hd := P.degree c
  rw [eq, P.core_card] at hd
  nlinarith

theorem distinguish (hq : 2 ≤ q) {x y : V} (hxy : x ≠ y) :
    ∃ E ∈ P.core, x ∈ E ∧ y ∉ E := by
  by_contra h
  push_neg at h
  have eq : P.core.filter (fun E => x ∈ E ∧ y ∈ E) = P.core.filter (x ∈ ·) := by
    ext E
    simp only [mem_filter]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · exact fun he => ⟨he.1, he.2, h E he.1 he.2⟩
  have hd := P.codegree x y hxy
  rw [eq, P.degree] at hd
  split_ifs at hd <;> omega

end Plane
end CoveringDesigns.TruncatedPlaneLoads
