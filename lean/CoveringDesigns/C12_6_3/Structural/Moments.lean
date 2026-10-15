import CoveringDesigns.C12_6_3.SmallBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import CoveringDesigns.Foundations.StandardAxioms

/-! Seven degree-seven points in a fifteen-block (12,6,3) cover contain a
triple belonging to at least two blocks.  The proof is elementary incidence
counting and does not use Stanton or the GPPT classification. -/

namespace CoveringDesigns.GPPTStructural

open Finset

variable {α : Type*} [DecidableEq α]

def containmentCount (C : Family α) (T : Finset α) : ℕ :=
  (C.filter (T ⊆ ·)).card

theorem containmentCount_pair (C : Family α) (p q : α) :
    containmentCount C {p, q} = degree (star C p) q := by
  unfold containmentCount degree star
  congr 1
  ext B
  simp [insert_subset_iff, singleton_subset_iff, and_comm, and_left_comm, and_assoc]

/-- Double-count the incidences between blocks and selected t-subsets. -/
theorem containment_moment (C : Family α) (S : Finset α) (t : ℕ) :
    (∑ T ∈ S.powersetCard t, containmentCount C T) =
      ∑ B ∈ C, (S ∩ B).card.choose t := by
  unfold containmentCount
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro B _
  have hf : (S.powersetCard t).filter (fun T => T ⊆ B) = (S ∩ B).powersetCard t := by
    ext T
    simp [subset_inter_iff, and_comm, and_assoc]
  rw [← sum_filter, ← card_eq_sum_ones, hf, card_powersetCard]
  simp

theorem point_incidence_moment (C : Family α) (S : Finset α) :
    (∑ p ∈ S, degree C p) = ∑ B ∈ C, (S ∩ B).card := by
  unfold degree star
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro B _
  rw [← sum_filter, filter_mem_eq_inter]

theorem pair_degree_at_least_three_12_6_3 [Fintype α]
    {C : Family α} (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    {p q : α} (hq : q ≠ p) : 3 ≤ degree (star C p) q := by
  have hh := degree_at_least_three_11_5_2
    (by rw [complement_point_card, hn]) (link_isCover hC p)
    (⟨q, hq⟩ : {q : α // q ≠ p})
  rwa [degree_link] at hh

theorem pair_containment_at_least_three_12_6_3 [Fintype α]
    {C : Family α} (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    {T : Finset α} (ht : T.card = 2) : 3 ≤ containmentCount C T := by
  obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp ht
  rw [containmentCount_pair]
  exact pair_degree_at_least_three_12_6_3 hn hC hpq.symm

/-- A six-point block must meet any seven points of a twelve-point set. -/
theorem seven_six_intersection_bounds [Fintype α] (hn : Fintype.card α = 12)
    {S B : Finset α} (hs : S.card = 7) (hb : B.card = 6) :
    1 ≤ (S ∩ B).card ∧ (S ∩ B).card ≤ 6 := by
  have hu : (S ∪ B).card ≤ 12 := by
    have hh := card_le_card (subset_univ (S ∪ B))
    rwa [card_univ, hn] at hh
  have hi := card_union_add_card_inter S B
  have hm := card_le_card (inter_subset_right : S ∩ B ⊆ B)
  omega

/-- This is the nonnegative polynomial (r-1)(r-3)(r-4), written using
binomial coefficients and verified at the six possible intersection sizes. -/
theorem intersection_moment_inequality {r : ℕ} (hlo : 1 ≤ r) (hhi : r ≤ 6) :
    10 * r.choose 2 + 12 ≤ 6 * r.choose 3 + 12 * r := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
  rcases hr with h | h | h | h | h | h <;> subst r <;> decide

/-- Any seven degree-seven points contain a repeated triple.  The pair
codegree lower bound of three follows from the covering property, so no
pair-equality hypothesis or classification theorem is needed. -/
theorem repeated_triple_of_seven_minimum_points [Fintype α]
    {C : Family α} (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hb : C.card = 15) {S : Finset α} (hs : S.card = 7)
    (hd : ∀ p ∈ S, degree C p = 7) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = 3 ∧ 2 ≤ containmentCount C T := by
  classical
  by_contra hnone
  have htriple (T : Finset α) (hT : T ∈ S.powersetCard 3) : containmentCount C T ≤ 1 := by
    have ht := mem_powersetCard.mp hT
    have hh : ¬ 2 ≤ containmentCount C T := fun h => hnone ⟨T, ht.1, ht.2, h⟩
    omega
  have hpoint : (∑ B ∈ C, (S ∩ B).card) = 49 := by
    rw [← point_incidence_moment]
    have hh := sum_const_nat hd
    simpa only [hs] using hh
  have hpair : 63 ≤ ∑ B ∈ C, (S ∩ B).card.choose 2 := by
    rw [← containment_moment]
    have hh := sum_le_sum (s := S.powersetCard 2) (fun T hT =>
      pair_containment_at_least_three_12_6_3 hn hC (mem_powersetCard.mp hT).2)
    have hc : Nat.choose 7 2 = 21 := by decide
    simpa only [sum_const, Nat.nsmul_eq_mul, card_powersetCard, hs, hc] using hh
  have htriples : (∑ B ∈ C, (S ∩ B).card.choose 3) ≤ 35 := by
    rw [← containment_moment]
    have hh := sum_le_sum (s := S.powersetCard 3) htriple
    have hc : Nat.choose 7 3 = 35 := by decide
    simpa only [sum_const, Nat.nsmul_eq_mul, card_powersetCard, hs, hc] using hh
  have hpoly := sum_le_sum (s := C) (fun B hB =>
    let hi := seven_six_intersection_bounds hn hs (hC.1 B hB)
    intersection_moment_inequality hi.1 hi.2)
  simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.nsmul_eq_mul, hb] at hpoly
  omega

theorem repeated_minimum_triple_of_seven_points [Fintype α]
    {C : Family α} (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hb : C.card = 15) (hm : 7 ≤ (minimumPoints C 7).card) :
    ∃ T : Finset α, T.card = 3 ∧ (∀ p ∈ T, degree C p = 7) ∧
      2 ≤ containmentCount C T := by
  obtain ⟨S, hs, hcard⟩ := exists_subset_card_eq hm
  have hd : ∀ p ∈ S, degree C p = 7 := by
    intro p hp
    exact (mem_filter.mp (hs hp)).2
  obtain ⟨T, ht, hc, hm⟩ := repeated_triple_of_seven_minimum_points hn hC hb hcard hd
  exact ⟨T, hc, fun p hp => hd p (ht hp), hm⟩

/-- A point of degree d forces at least d-2 minimum points, by counting the
degrees at the eleven other points. -/
theorem degree_le_minimum_points_add_two_12_6_3 [Fintype α]
    {C : Family α} (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hb : C.card = 15) (p : α) : degree C p ≤ (minimumPoints C 7).card + 2 := by
  let S := (univ : Finset α).erase p
  let M := S.filter (fun q => degree C q = 7)
  have hS : S.card = 11 := by
    dsimp [S]
    rw [card_erase_of_mem (mem_univ p), card_univ, hn]
  have htotal : (∑ q ∈ S, degree C q) + degree C p = 90 := by
    have he := sum_erase_add (univ : Finset α) (degree C) (mem_univ p)
    have ht := degree_sum_of_uniform hC.1
    rw [hb] at ht
    exact he.trans ht
  have hM : (∑ q ∈ S, if degree C q = 7 then 1 else 0) = M.card := by
    simp only [M, card_eq_sum_ones, sum_filter]
  have hcount : 88 ≤ (∑ q ∈ S, degree C q) + M.card := by
    have hpoint (q : α) : 8 ≤ degree C q + if degree C q = 7 then 1 else 0 := by
      have hl := degree_at_least_seven_12_6_3 hn hC q
      split_ifs <;> omega
    have hh := sum_le_sum (s := S) (fun q _ => hpoint q)
    simpa only [sum_const, Nat.nsmul_eq_mul, hS, sum_add_distrib, hM] using hh
  have hm : M.card ≤ (minimumPoints C 7).card := by
    apply card_le_card
    intro q hq
    exact mem_filter.mpr ⟨mem_univ q, (mem_filter.mp hq).2⟩
  omega

theorem repeated_minimum_triple_of_degree_at_least_nine [Fintype α]
    {C : Family α} (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hb : C.card = 15) {p : α} (hp : 9 ≤ degree C p) :
    ∃ T : Finset α, T.card = 3 ∧ (∀ q ∈ T, degree C q = 7) ∧
      2 ≤ containmentCount C T := by
  have hh := degree_le_minimum_points_add_two_12_6_3 hn hC hb p
  exact repeated_minimum_triple_of_seven_points hn hC hb (by omega)

/-- The branch of GPPT 5.9 in which each triple of minimum-degree points
occurs at most once. Coverage supplies the corresponding lower bound. -/
def NoDuplicateMinimumTriple (C : Family α) : Prop :=
  ∀ T : Finset α, T.card = 3 → (∀ p ∈ T, degree C p = 7) →
    containmentCount C T ≤ 1

/-- At most six excess incidences are available in a cover of at most fifteen blocks. -/
theorem total_excess_le_six [Fintype α] {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15) :
    (∑ p : α, (degree C p - 7)) ≤ 6 := by
  have he : (∑ p : α, (degree C p - 7)) + ∑ _p : α, 7 = ∑ p : α, degree C p := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    exact Nat.sub_add_cancel (degree_at_least_seven_12_6_3 hn hC p)
  rw [sum_const, card_univ, hn, Nat.nsmul_eq_mul, degree_sum_of_uniform hC.1] at he
  omega

/-- The six excess incidences are the entire budget above degree seven. -/
theorem total_excess_six [Fintype α] {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card = 15) :
    (∑ p : α, (degree C p - 7)) = 6 := by
  have he : (∑ p : α, (degree C p - 7)) + ∑ _p : α, 7 = ∑ p : α, degree C p := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    exact Nat.sub_add_cancel (degree_at_least_seven_12_6_3 hn hC p)
  rw [sum_const, card_univ, hn, Nat.nsmul_eq_mul, degree_sum_of_uniform hC.1, hb] at he
  omega

/-- Without a repeated minimum triple, there are exactly six minimum points.
The seven-point moment obstruction replaces a longer excess argument. -/
theorem no_duplicate_minimum_points_card [Fintype α]
    {C : Family α} (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hb : C.card = 15) (hno : NoDuplicateMinimumTriple C) :
    (minimumPoints C 7).card = 6 := by
  have hlo := minimum_points_bound hC.1 (degree_at_least_seven_12_6_3 hn hC)
  rw [hn, hb] at hlo
  have hhi : (minimumPoints C 7).card ≤ 6 := by
    by_contra h
    obtain ⟨T, ht, hd, hm⟩ := repeated_minimum_triple_of_seven_points hn hC hb (by omega)
    have := hno T ht hd
    omega
  omega

/-- In this branch every other point has degree eight. -/
theorem no_duplicate_degree_seven_or_eight [Fintype α]
    {C : Family α} (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hb : C.card = 15) (hno : NoDuplicateMinimumTriple C) (p : α) :
    degree C p = 7 ∨ degree C p = 8 := by
  have hlo := degree_at_least_seven_12_6_3 hn hC p
  have hhi : degree C p ≤ 8 := by
    by_contra h
    obtain ⟨T, ht, hd, hm⟩ :=
      repeated_minimum_triple_of_degree_at_least_nine hn hC hb (by omega : 9 ≤ degree C p)
    have := hno T ht hd
    omega
  omega

theorem no_duplicate_degree_eight_card [Fintype α]
    {C : Family α} (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hb : C.card = 15) (hno : NoDuplicateMinimumTriple C) :
    (minimumPoints C 8).card = 6 := by
  have hs := card_filter_add_card_filter_not (s := (univ : Finset α))
    (p := fun p => degree C p = 7)
  have he : univ.filter (fun p => ¬ degree C p = 7) = minimumPoints C 8 := by
    ext p
    have hd := no_duplicate_degree_seven_or_eight hn hC hb hno p
    simp only [minimumPoints, mem_filter, mem_univ, true_and]
    omega
  rw [he, card_univ, hn] at hs
  change (minimumPoints C 7).card + (minimumPoints C 8).card = 12 at hs
  rw [no_duplicate_minimum_points_card hn hC hb hno] at hs
  omega

#guard_standard_axioms containment_moment repeated_triple_of_seven_minimum_points
  repeated_minimum_triple_of_degree_at_least_nine total_excess_le_six total_excess_six
  no_duplicate_minimum_points_card no_duplicate_degree_seven_or_eight
  no_duplicate_degree_eight_card

end CoveringDesigns.GPPTStructural
