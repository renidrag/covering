import CoveringDesigns.C13_7_4.Structural.Basic
import Mathlib.Tactic.IntervalCases

/-! The final five-point count, separated from the local compatibility proof. -/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural

variable {α : Type*} [DecidableEq α]

/-- The fourth Bonferroni inequality for at most five incidences. These six
scalar arithmetic cases are independent of any covering configuration. -/
theorem five_point_bonferroni (r : ℕ) (hr : r ≤ 5) :
    r + r.choose 3 ≤ 1 + r.choose 2 + r.choose 4 := by
  interval_cases r <;> decide

/-- The 15/7/3/1 profile on five points requires at least thirty blocks. -/
theorem five_point_count (C : Family α) (M : Finset α) (hM : M.card = 5)
    (hd : ∀ p ∈ M, degree C p = 15)
    (hpair : ∀ T ∈ M.powersetCard 2, containmentCount C T = 7)
    (htriple : ∀ T ∈ M.powersetCard 3, containmentCount C T = 3)
    (hquad : ∀ T ∈ M.powersetCard 4, containmentCount C T = 1) :
    30 ≤ C.card := by
  have hpoint : (∑ B ∈ C, (M ∩ B).card) = 75 := by
    rw [← point_incidence_moment, sum_const_nat hd, hM]
  have moment (t v : ℕ)
      (h : ∀ T ∈ M.powersetCard t, containmentCount C T = v) :
      (∑ B ∈ C, (M ∩ B).card.choose t) = (5 : ℕ).choose t * v := by
    rw [← containment_moment, sum_const_nat h, card_powersetCard, hM]
  have hp : (∑ B ∈ C, (M ∩ B).card.choose 2) = 70 := moment 2 7 hpair
  have ht : (∑ B ∈ C, (M ∩ B).card.choose 3) = 30 := moment 3 3 htriple
  have hq : (∑ B ∈ C, (M ∩ B).card.choose 4) = 5 := moment 4 1 hquad
  have hi := sum_le_sum (s := C) (fun B _ =>
    five_point_bonferroni (M ∩ B).card
      ((card_le_card inter_subset_left).trans_eq hM))
  simp only [sum_add_distrib, sum_const, Nat.nsmul_eq_mul, mul_one] at hi
  omega

variable [Fintype α]

/-- This interface isolates the two new compatibility obligations. It is
assembled into an unconditional theorem only after both are proved. -/
theorem lower_bound_of_pair_quad_obstructions {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (hpairs : ∀ p q, p ≠ q → degree C p = 15 → degree C q = 15 →
      degree (star C p) q = 7)
    (hquads : ∀ K : Finset α, K.card = 4 →
      (∀ p ∈ K, degree C p = 15) → containmentCount C K ≠ 3) :
    30 ≤ C.card := by
  by_cases hb : C.card ≤ 29
  · obtain ⟨M, hsub, hM⟩ := exists_subset_card_eq (five_minimum_points hn hC hb)
    have hd (p : α) (hp : p ∈ M) : degree C p = 15 :=
      (mem_filter.mp (hsub hp)).2
    apply five_point_count C M hM hd
    · intro T hT
      obtain ⟨hTM, hc⟩ := mem_powersetCard.mp hT
      obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp hc
      rw [containmentCount_pair]
      exact hpairs p q hpq (hd p (hTM (by simp))) (hd q (hTM (by simp)))
    · intro T hT
      obtain ⟨hTM, hc⟩ := mem_powersetCard.mp hT
      obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp hc
      have hp := hd p (hTM (by simp))
      have hq := hd q (hTM (by simp))
      have hr := hd r (hTM (by simp))
      exact minimum_triple_count hn hC hp hpq hpr hqr
        (hpairs p q hpq hp hq) (hpairs p r hpr hp hr)
    · intro T hT
      obtain ⟨hTM, hc⟩ := mem_powersetCard.mp hT
      have hnot := hquads T hc (fun p hp => hd p (hTM hp))
      obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := card_eq_four.mp hc
      have hp := hd p (hTM (by simp))
      have hq := hd q (hTM (by simp))
      have hr := hd r (hTM (by simp))
      have hs := hd s (hTM (by simp))
      exact (minimum_quad_count_one_or_three hn hC hp hpq hpr hps hqr hqs hrs
        (hpairs p q hpq hp hq) (hpairs p r hpr hp hr)
        (hpairs p s hps hp hs)).resolve_right hnot
  · omega

#guard_standard_axioms five_point_bonferroni five_point_count
  lower_bound_of_pair_quad_obstructions

end CoveringDesigns.C13Structural
