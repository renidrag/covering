import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
Finite coverings and general incidence counting.
No classification theorem is assumed in this file.
-/

namespace CoveringDesigns

open Finset

abbrev Family (α : Type*) := Finset (Finset α)

def Uniform {α : Type*} (C : Family α) (k : ℕ) : Prop :=
  ∀ B ∈ C, B.card = k

def Covers {α : Type*} (C : Family α) (t : ℕ) : Prop :=
  ∀ T : Finset α, T.card = t → ∃ B ∈ C, T ⊆ B

def IsCover {α : Type*} (C : Family α) (k t : ℕ) : Prop :=
  Uniform C k ∧ Covers C t

def star {α : Type*} [DecidableEq α] (C : Family α) (p : α) : Family α :=
  C.filter (p ∈ ·)

def degree {α : Type*} [DecidableEq α] (C : Family α) (p : α) : ℕ :=
  (star C p).card

def minimumPoints {α : Type*} [Fintype α] [DecidableEq α]
    (C : Family α) (m : ℕ) : Finset α :=
  univ.filter (degree C · = m)

theorem covers_of_powersetCard {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} {t : ℕ}
    (h : ∀ T ∈ (univ : Finset α).powersetCard t, ∃ B ∈ C, T ⊆ B) :
    Covers C t := by
  intro T ht
  exact h T (mem_powersetCard_univ.mpr ht)

theorem degree_sum {α : Type*} [Fintype α] [DecidableEq α] (C : Family α) :
    ∑ p, degree C p = ∑ B ∈ C, B.card := by
  simp only [degree, star, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp

theorem degree_sum_of_uniform {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} {k : ℕ} (h : Uniform C k) :
    ∑ p, degree C p = k * C.card := by
  rw [degree_sum, sum_const_nat h, Nat.mul_comm]

theorem minimum_points_bound {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} {k m : ℕ} (hu : Uniform C k)
    (hl : ∀ p, m ≤ degree C p) :
    Fintype.card α * (m + 1) ≤ k * C.card + (minimumPoints C m).card := by
  have hp (p : α) : m + 1 ≤ degree C p + if degree C p = m then 1 else 0 := by
    split_ifs with he
    · omega
    · have := hl p
      omega
  have hs := sum_le_sum (s := (univ : Finset α)) (fun p _ => hp p)
  have hm : (∑ p : α, if degree C p = m then 1 else 0) =
      (minimumPoints C m).card := by
    simp only [minimumPoints, card_eq_sum_ones, sum_filter]
  simpa [sum_add_distrib, degree_sum_of_uniform hu, hm] using hs

end CoveringDesigns
