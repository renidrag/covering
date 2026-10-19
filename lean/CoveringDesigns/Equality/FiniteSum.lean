import CoveringDesigns.Schoenheim.LowerBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! Finite nonnegative budgets and their small-budget profiles. -/
namespace CoveringDesigns.Equality
open Finset
variable {ι : Type*}

/-- A positive threshold consumes that many units at each qualifying row. -/
theorem threshold_count_le (S : Finset ι) (f : ι → ℕ) (j : ℕ) :
    j * (S.filter (fun x => j ≤ f x)).card ≤ ∑ x ∈ S, f x := by
  calc
    j * (S.filter (fun x => j ≤ f x)).card =
        ∑ x ∈ S.filter (fun x => j ≤ f x), j := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S.filter (fun x => j ≤ f x), f x :=
      sum_le_sum (fun x hx => (mem_filter.mp hx).2)
    _ ≤ ∑ x ∈ S, f x := sum_le_sum_of_subset (filter_subset _ _)

theorem budget_zero {S : Finset ι} {f : ι → ℕ} (h : ∑ x ∈ S, f x = 0) :
    ∀ x ∈ S, f x = 0 := by
  intro x hx
  have := single_le_sum (fun y _ => Nat.zero_le (f y)) hx
  omega

theorem budget_one {S : Finset ι} {f : ι → ℕ} (h : ∑ x ∈ S, f x = 1) :
    ∃ p ∈ S, f p = 1 ∧ ∀ q ∈ S, q ≠ p → f q = 0 := by
  classical
  have hp : ∃ p ∈ S, 0 < f p := by
    by_contra hn
    push Not at hn
    have hz : ∑ x ∈ S, f x = 0 := by
      apply sum_eq_zero; intro x hx; exact Nat.eq_zero_of_le_zero (hn x hx)
    omega
  obtain ⟨p, hp, hpos⟩ := hp
  have hle := single_le_sum (fun y _ => Nat.zero_le (f y)) hp
  have he : f p = 1 := by omega
  have her : ∑ q ∈ S.erase p, f q = 0 := by
    have := sum_erase_add S f hp
    omega
  exact ⟨p, hp, he, fun q hq hqp => budget_zero her q (mem_erase.mpr ⟨hqp, hq⟩)⟩

theorem budget_two {S : Finset ι} {f : ι → ℕ} (h : ∑ x ∈ S, f x = 2) :
    (∃ p ∈ S, f p = 2 ∧ ∀ q ∈ S, q ≠ p → f q = 0) ∨
    (∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ f p = 1 ∧ f q = 1 ∧
      ∀ z ∈ S, z ≠ p → z ≠ q → f z = 0) := by
  classical
  by_cases ht : ∃ p ∈ S, f p = 2
  · obtain ⟨p, hp, he⟩ := ht
    have her : ∑ q ∈ S.erase p, f q = 0 := by
      have := sum_erase_add S f hp
      omega
    exact Or.inl ⟨p, hp, he, fun q hq hqp => budget_zero her q (mem_erase.mpr ⟨hqp, hq⟩)⟩
  · have hp : ∃ p ∈ S, 0 < f p := by
      by_contra hn
      push Not at hn
      have hz : ∑ x ∈ S, f x = 0 := by
        apply sum_eq_zero; intro x hx; exact Nat.eq_zero_of_le_zero (hn x hx)
      omega
    obtain ⟨p, hp, hpos⟩ := hp
    have hle := single_le_sum (fun y _ => Nat.zero_le (f y)) hp
    have hne : f p ≠ 2 := fun he => ht ⟨p, hp, he⟩
    have he : f p = 1 := by omega
    have her : ∑ q ∈ S.erase p, f q = 1 := by
      have := sum_erase_add S f hp
      omega
    obtain ⟨q, hq, hqe, hrest⟩ := budget_one her
    exact Or.inr ⟨p, hp, q, (mem_erase.mp hq).2, (mem_erase.mp hq).1.symm,
      he, hqe, fun z hz hzp hzq => hrest z (mem_erase.mpr ⟨hzp, hz⟩) hzq⟩

/-- Casting the natural excesses is exact when every row meets its baseline. -/
theorem excess_sum_cast {S : Finset ι} {u : ι → ℕ} {m : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) :
    (↑(∑ x ∈ S, (u x - m)) : ℤ) = (∑ x ∈ S, (u x : ℤ)) - S.card * m := by
  rw [Nat.cast_sum]
  calc
    _ = ∑ x ∈ S, ((u x : ℤ) - m) :=
      sum_congr rfl (fun x hx => Nat.cast_sub (hl x hx))
    _ = _ := by simp [sum_sub_distrib]


/-- The signed remainder at a rounded ceiling is nonnegative and less than the divisor. -/
theorem ceiling_remainder {n k : ℕ} (hk : 0 < k) :
    0 ≤ (k : ℤ) * Schoenheim.ceilDiv n k - n ∧
      (k : ℤ) * Schoenheim.ceilDiv n k - n < k := by
  have hl : n ≤ k * Schoenheim.ceilDiv n k :=
    (Schoenheim.ceilDiv_le_iff hk).mp le_rfl
  have hu : k * Schoenheim.ceilDiv n k < n + k := by
    by_cases hc : Schoenheim.ceilDiv n k = 0
    · simp [hc]; omega
    · have hp : k * (Schoenheim.ceilDiv n k - 1) < n := by
        by_contra hn
        have := (Schoenheim.ceilDiv_le_iff hk).mpr (Nat.le_of_not_gt hn)
        omega
      have he : Schoenheim.ceilDiv n k - 1 + 1 = Schoenheim.ceilDiv n k := by omega
      nlinarith
  constructor <;> exact_mod_cast (by omega : _)

end CoveringDesigns.Equality
