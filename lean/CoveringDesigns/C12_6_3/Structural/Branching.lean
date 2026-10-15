import CoveringDesigns.C12_6_3.Structural.MinimumPairs

/-! The elementary lower bound and branch point of the structural GPPT proof.
The pair-degree lemma rules out fourteen blocks. A repeated minimum triple
then occurs exactly three times and supplies a three-star frame. -/

namespace CoveringDesigns.GPPTStructural

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Fourteen blocks would make every point minimum. Each link would then
have eleven degree-three points, contradicting its thirty-five incidences. -/
theorem lower_bound_fifteen {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) : 15 ≤ C.card := by
  by_contra h
  have hb : C.card ≤ 14 := by omega
  have hM := minimum_points_bound hC.1 (degree_at_least_seven_12_6_3 hn hC)
  rw [hn] at hM
  have hMe : minimumPoints C 7 = univ :=
    eq_of_subset_of_card_le (subset_univ _) (by rw [card_univ, hn]; omega)
  have hd (p : α) : degree C p = 7 := by
    have hp : p ∈ minimumPoints C 7 := by rw [hMe]; exact mem_univ _
    exact (mem_filter.mp hp).2
  obtain ⟨p⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
  have hq (q : {q : α // q ≠ p}) : degree (link C p) q = 3 := by
    rw [degree_link]
    exact minimum_pair_degree_three hn hC (by omega) (hd p) (hd q.val) q.property.symm
  have hs := degree_sum_of_uniform (link_isCover hC p).1
  simp only [hq, sum_const, card_univ, complement_point_card, hn,
    Nat.nsmul_eq_mul, link_card, hd] at hs
  omega

omit [Fintype α] in
theorem containmentCount_triple (C : Family α) (p q r : α) :
    containmentCount C {p, q, r} = degree (star (star C p) q) r := by
  unfold containmentCount degree star
  congr 1
  ext B
  simp [insert_subset_iff, singleton_subset_iff, and_assoc]

/-- In the link of a minimum point, multiplicity two would force one of
the other two columns to have degree four, contrary to the pair lemma. -/
theorem minimum_triple_not_two {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15)
    {p q r : α} (hp : degree C p = 7) (hq : degree C q = 7) (hr : degree C r = 7)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    containmentCount C {p, q, r} ≠ 2 := by
  let q' : {x : α // x ≠ p} := ⟨q, hpq.symm⟩
  let r' : {x : α // x ≠ p} := ⟨r, hpr.symm⟩
  have hq' : degree (link C p) q' = 3 := by
    rw [degree_link]
    exact minimum_pair_degree_three hn hC hb hp hq hpq
  have hr' : degree (link C p) r' = 3 := by
    rw [degree_link]
    exact minimum_pair_degree_three hn hC hb hp hr hpr
  have hmult : StantonGeometry.multiplicity (link C p) {q', r'} =
      containmentCount C {p, q, r} := by
    change containmentCount (link C p) {q', r'} = _
    rw [containmentCount_pair, star_link, degree_link, containmentCount_triple]
    unfold degree star
    congr 1
    ext B
    simp [q', r', and_comm, and_left_comm]
  intro ht
  have hF := StantonGeometry.geometry_facts
    (by rw [complement_point_card, hn]) (link_isCover hC p) (by rwa [link_card])
  have hne : q' ≠ r' := fun h => hqr (congrArg Subtype.val h)
  rcases hF.multiplicity_two_free q' r' hne (hmult.trans ht) with h | h <;> omega

/-- Repetition of a minimum-point triple means multiplicity three. -/
theorem repeated_minimum_triple_count {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15)
    {T : Finset α} (ht : T.card = 3) (hd : ∀ p ∈ T, degree C p = 7)
    (hr : 2 ≤ containmentCount C T) : containmentCount C T = 3 := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp ht
  have hp := hd p (by simp)
  have hq := hd q (by simp)
  have hr' := hd r (by simp)
  have hne := minimum_triple_not_two hn hC hb hp hq hr' hpq hpr hqr
  have hsub : C.filter ({p, q, r} ⊆ ·) ⊆ C.filter ({p, q} ⊆ ·) := by
    intro B hB
    obtain ⟨hBC, hs⟩ := mem_filter.mp hB
    exact mem_filter.mpr ⟨hBC, (by simp : ({p, q} : Finset α) ⊆ {p, q, r}).trans hs⟩
  have hle := card_le_card hsub
  change containmentCount C {p, q, r} ≤ containmentCount C {p, q} at hle
  rw [containmentCount_pair, minimum_pair_degree_three hn hC hb hp hq hpq] at hle
  omega

/-- The repeated-triple branch of Theorem 5.9 admits the structural
three-star coordinates. No classification of covers is used here. -/
theorem triplicate_frame_of_not_noDuplicate {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15)
    (hno : ¬ NoDuplicateMinimumTriple C) : Nonempty (TriplicateFrame C) := by
  classical
  simp only [NoDuplicateMinimumTriple, not_forall, not_le] at hno
  obtain ⟨T, ht, hd, hm⟩ := hno
  have hthree := repeated_minimum_triple_count hn hC hb ht hd (by omega)
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp ht
  let roots : Fin 3 → α := ![p, q, r]
  have hi : Function.Injective roots := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [roots]
  have hd' : ∀ i, degree C (roots i) = 7 := by
    intro i
    apply hd
    fin_cases i <;> simp [roots]
  have hpair : ∀ i j, i ≠ j → degree (star C (roots i)) (roots j) = 3 := by
    intro i j hij
    exact minimum_pair_degree_three hn hC hb (hd' i) (hd' j) (fun h => hij (hi h))
  apply exists_triplicate_frame hn hC hb roots hi hd' hpair
  have he : univ.image roots = {p, q, r} := by
    ext x
    simp [roots, Fin.exists_fin_succ, eq_comm]
  simpa only [he, commonBlocks, containmentCount] using hthree

#guard_standard_axioms lower_bound_fifteen minimum_triple_not_two
  repeated_minimum_triple_count triplicate_frame_of_not_noDuplicate

end CoveringDesigns.GPPTStructural
