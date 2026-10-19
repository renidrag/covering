import CoveringDesigns.TwoKMinusTwoEquality.Matrix
import CoveringDesigns.TwoKMinusTwo.Rank

/-! Actual low-point incidence rigidity in the two-k-minus-two family.
The representative argument uses the real incidence matrix of the given blocks.
Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusTwoEquality
open Finset Matrix TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

/-- Every actual low-point row has six ones. -/
theorem low_row_sum (C : Family α) (x : Low C) :
    ∑ B : C, lowIncidence C x B = (6 : ℝ) := by
  have hx : degree C x.val = 6 := (mem_filter.mp x.property).2
  have he : (∑ B : C, lowIncidence C x B) = (degree C x.val : ℝ) := by
    simp only [lowIncidence, degree, star, card_eq_sum_ones, sum_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [sum_coe_sort C (fun B => if x.val ∈ B then (1 : ℝ) else 0)]
  rw [he, hx]
  norm_num

/-- The equality case has eleven actual blocks, zero deficits, and paired
identical supports. No triple-cover or universal point-floor assumption
is required for this structural lemma. -/
theorem low_equality_rigidity {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hu : Uniform C k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (heq : (minimumPoints C 6).card = 2*C.card) :
    C.card = 11 ∧ (∀ x : Low C, deficit C x = 0) ∧
      ∃ e : C × Bool ≃ Low C, ∀ i B : C,
        ((e (i,false)).val ∈ B.val ↔ (e (i,true)).val ∈ B.val) := by
  have hb : 0 < Fintype.card C := by
    obtain ⟨p,q,hpq⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
    have hp := hpair p q hpq
    have hd : degree (star C p) q ≤ C.card := by
      exact (card_filter_le _ _).trans (card_filter_le _ _)
    simpa only [Fintype.card_coe] using (by omega : 0 < C.card)
  have hcard : Fintype.card (Low C) = 2 * Fintype.card C := by
    simpa only [Fintype.card_coe] using heq
  have hdata := boundary_parameter (lowIncidence C) 6 3 (lowExcess C) (deficit C)
    (by norm_num) (by norm_num) hb
    (by
      intro x y
      simp [lowExcess, excess, eq_comm, pair_degree_comm C x.val y.val])
    (fun x y => excess_nonneg hpair x.val y.val)
    (by intro x; simp [lowExcess, excess])
    (fun x => sub_nonneg.mpr (low_row_le hv hk hu hpair x))
    (by intro x; dsimp [deficit]; ring)
    (low_row_sum C)
    (by norm_num; exact low_gram)
    hcard
  obtain ⟨hd,⟨e,he,_⟩,hparam⟩ := hdata
  have hbR : (C.card : ℝ) = 11 := by
    simp only [Fintype.card_coe] at hparam
    linarith
  refine ⟨by exact_mod_cast hbR, hd, e, ?_⟩
  intro i B
  have h := he i B
  by_cases hx : (e (i,false)).val ∈ B.val <;>
    by_cases hy : (e (i,true)).val ∈ B.val <;>
    simp_all [lowIncidence]

/-- The numerical consequence needed by the two endpoint exclusions. -/
theorem card_eleven_of_low_equality {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hu : Uniform C k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (heq : (minimumPoints C 6).card = 2*C.card) : C.card = 11 :=
  (low_equality_rigidity hv hk hu hpair heq).1

end CoveringDesigns.TwoKMinusTwoEquality
