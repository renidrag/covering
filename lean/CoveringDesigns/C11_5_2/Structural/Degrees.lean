import CoveringDesigns.C11_5_2.SmallBounds
import CoveringDesigns.Foundations.Intersecting
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Elementary degree structure of seven-block pair coverings on eleven points.
This module uses incidence counting and the intersecting-triples inequality,
without using the Stanton classification or a computational certificate. -/

namespace CoveringDesigns

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The 35 incidences leave exactly two incidences above the pointwise lower bound. -/
theorem structural_degree_excess_sum {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7) :
    ∑ p, (degree C p - 3) = 2 := by
  have hl := degree_at_least_three_11_5_2 hn h
  have hs := degree_sum_of_uniform h.1
  rw [hC] at hs
  have he : (∑ p, (degree C p - 3)) + 33 = 35 := by
    calc
      (∑ p, (degree C p - 3)) + 33 = ∑ p, ((degree C p - 3) + 3) := by
        simp [sum_add_distrib, hn]
      _ = ∑ p, degree C p := sum_congr rfl fun p _ => Nat.sub_add_cancel (hl p)
      _ = 35 := hs
  omega

theorem structural_degree_at_most_five {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7) (p : α) :
    degree C p ≤ 5 := by
  have hx : degree C p - 3 ≤ ∑ q, (degree C q - 3) :=
    single_le_sum (f := fun q => degree C q - 3)
      (fun _ _ => Nat.zero_le _) (mem_univ p)
  rw [structural_degree_excess_sum hn h hC] at hx
  omega

theorem structural_two_point_excess {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    {p q : α} (hpq : p ≠ q) : (degree C p - 3) + (degree C q - 3) ≤ 2 := by
  have hx : (∑ x ∈ ({p, q} : Finset α), (degree C x - 3)) ≤
      ∑ x, (degree C x - 3) := sum_le_sum_of_subset (subset_univ _)
  simpa [hpq, structural_degree_excess_sum hn h hC] using hx

theorem structural_degree_five_others {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    {p : α} (hp : degree C p = 5) {q : α} (hpq : p ≠ q) : degree C q = 3 := by
  have hx := structural_two_point_excess hn h hC hpq
  have hl := degree_at_least_three_11_5_2 hn h q
  omega

/-- A point's incidence set, with blocks as vertices. -/
def structural_incidentRows (C : Family α) (p : α) : Finset C :=
  univ.filter fun B => p ∈ B.val

omit [Fintype α] in
theorem structural_incidentRows_card (C : Family α) (p : α) :
    (structural_incidentRows C p).card = degree C p := by
  unfold structural_incidentRows degree star
  apply card_bij (fun B _ => B.val)
  · intro B hB
    exact mem_filter.mpr ⟨B.property, (mem_filter.mp hB).2⟩
  · intro B hB D hD hBD
    exact Subtype.ext hBD
  · intro B hB
    exact ⟨⟨B, (mem_filter.mp hB).1⟩, by simpa using (mem_filter.mp hB).2, rfl⟩

omit [Fintype α] in
theorem structural_incidentRows_meet {C : Family α} (h : IsCover C 5 2)
    {p q : α} (hpq : p ≠ q) :
    (structural_incidentRows C p ∩ structural_incidentRows C q).Nonempty := by
  obtain ⟨B, hB, hpqB⟩ := h.2 {p, q} (by simp [hpq])
  refine ⟨⟨B, hB⟩, ?_⟩
  have hpB : p ∈ B := hpqB (by simp)
  have hqB : q ∈ B := hpqB (by simp)
  simp [structural_incidentRows, hpB, hqB]

omit [Fintype α] in
/-- Restricting point indices to `L` gives the intersection size as each row degree. -/
theorem structural_indexed_row_card (C : Family α) (L : Finset α) (B : C) :
    (univ.filter (fun p : L => B ∈ structural_incidentRows C p.val)).card =
      (B.val ∩ L).card := by
  apply card_bij (fun p _ => p.val)
  · intro p hp
    exact mem_inter.mpr ⟨by simpa [structural_incidentRows] using (mem_filter.mp hp).2,
      p.property⟩
  · intro p hp q hq hpq
    exact Subtype.ext hpq
  · intro p hp
    refine ⟨⟨p, (mem_inter.mp hp).2⟩, ?_, rfl⟩
    simpa [structural_incidentRows] using (mem_inter.mp hp).1

omit [Fintype α] in
theorem structural_row_incidence_sum (C : Family α) (L : Finset α) :
    ∑ B : C, (B.val ∩ L).card = ∑ p ∈ L, degree C p := by
  rw [show (∑ B : C, (B.val ∩ L).card) = ∑ B ∈ C, (B ∩ L).card from
    sum_coe_sort C (fun B => (B ∩ L).card)]
  have hc (B : Finset α) : (B ∩ L).card = ∑ p ∈ L, if p ∈ B then 1 else 0 := by
    rw [← sum_filter, ← card_eq_sum_ones]
    congr 1
    ext p
    simp [and_comm]
  simp_rw [hc]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  simp only [degree, star, card_eq_sum_ones, sum_filter]

/-- The degree-five pattern would give total vertex-pair incidence 50. -/
theorem structural_degree_five_pair_sum {C : Family α}
    (h : IsCover C 5 2) (hC : C.card = 7) {p : α} (hp : degree C p = 5) :
    (∑ B : C, ((B.val ∩ univ.erase p).card).choose 2) = 50 := by
  have hv : Fintype.card C = 7 := by simpa using hC
  have hc : (univ.filter (fun B : C => p ∈ B.val)).card = 5 := by
    simpa [structural_incidentRows] using (structural_incidentRows_card C p).trans hp
  have hnc : (univ.filter (fun B : C => p ∉ B.val)).card = 2 := by
    have he := card_filter_add_card_filter_not (s := (univ : Finset C))
      (p := fun B => p ∈ B.val)
    simp only [card_univ, hv, hc] at he
    omega
  have hb (B : C) : (B.val ∩ univ.erase p).card = if p ∈ B.val then 4 else 5 := by
    have he : B.val ∩ univ.erase p = B.val.erase p := by
      ext q
      simp [and_comm]
    rw [he]
    split_ifs with hm
    · rw [card_erase_of_mem hm, h.1 B.val B.property]
    · rw [erase_eq_of_notMem hm, h.1 B.val B.property]
  calc
    (∑ B : C, ((B.val ∩ univ.erase p).card).choose 2) =
        ∑ B : C, if p ∈ B.val then 6 else 10 := by
      apply sum_congr rfl
      intro B _
      rw [hb]
      split_ifs <;> decide
    _ = 50 := by
      have he (B : C) : (if p ∈ B.val then 6 else 10) =
          (if p ∈ B.val then 6 else 0) + (if p ∉ B.val then 10 else 0) := by
        split_ifs <;> simp_all
      simp_rw [he]
      rw [sum_add_distrib, ← sum_filter, ← sum_filter]
      simp only [sum_const, hc, hnc]
      decide

private theorem degree_bound_of_triples_inequality {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    (ht : ∀ L : Finset α, (∀ p ∈ L, degree C p = 3) →
      L.card.choose 2 + 2 * L.card ≤ (∑ B : C, ((B.val ∩ L).card).choose 2) + 14)
    (p : α) : degree C p ≤ 4 := by
  by_contra hg
  have hp : degree C p = 5 := by
    have hu := structural_degree_at_most_five hn h hC p
    omega
  have hl : ∀ q ∈ (univ.erase p : Finset α), degree C q = 3 := by
    intro q hq
    exact structural_degree_five_others hn h hC hp (mem_erase.mp hq).1.symm
  have hb := ht (univ.erase p) hl
  have hcard : (univ.erase p : Finset α).card = 10 := by simp [hn]
  rw [hcard, structural_degree_five_pair_sum h hC hp] at hb
  have hchoose : Nat.choose 10 2 = 45 := by decide
  rw [hchoose] at hb
  omega

private theorem degree_four_card_of_bound {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    (hu : ∀ p, degree C p ≤ 4) : (univ.filter fun p => degree C p = 4).card = 2 := by
  rw [← structural_degree_excess_sum hn h hC]
  rw [card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro p _
  have hl := degree_at_least_three_11_5_2 hn h p
  have hp := hu p
  split_ifs <;> omega

private theorem degree_three_card_of_bound {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    (hu : ∀ p, degree C p ≤ 4) : (univ.filter fun p => degree C p = 3).card = 9 := by
  have hf := degree_four_card_of_bound hn h hC hu
  have he := card_filter_add_card_filter_not (s := (univ : Finset α))
    (p := fun p => degree C p = 3)
  have hnot : (univ.filter fun p => ¬ degree C p = 3) =
      (univ.filter fun p => degree C p = 4) := by
    ext p
    have hl := degree_at_least_three_11_5_2 hn h p
    have hp := hu p
    simp only [mem_filter, mem_univ, true_and]
    omega
  rw [hnot, hf, card_univ, hn] at he
  omega

private theorem all_low_block_of_triples_inequality {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    (hu : ∀ p, degree C p ≤ 4)
    (ht : ∀ L : Finset α, (∀ p ∈ L, degree C p = 3) →
      L.card.choose 2 + 2 * L.card ≤ (∑ B : C, ((B.val ∩ L).card).choose 2) + 14) :
    ∃ A ∈ C, ∀ p ∈ A, degree C p = 3 := by
  by_contra hno
  let L : Finset α := univ.filter fun p => degree C p = 3
  let H : Finset α := univ.filter fun p => degree C p = 4
  have hL : L.card = 9 := degree_three_card_of_bound hn h hC hu
  have hH : H.card = 2 := degree_four_card_of_bound hn h hC hu
  have hv : Fintype.card C = 7 := by simpa using hC
  have hnot (p : α) : degree C p ≠ 3 ↔ degree C p = 4 := by
    have hl := degree_at_least_three_11_5_2 hn h p
    have hp := hu p
    omega
  have hsumH : ∑ B : C, (B.val ∩ H).card = 8 := by
    rw [structural_row_incidence_sum]
    calc
      (∑ p ∈ H, degree C p) = ∑ _p ∈ H, 4 := by
        apply sum_congr rfl
        intro p hp
        exact (mem_filter.mp hp).2
      _ = 8 := by simp [hH]
  have hparts (B : C) : (B.val ∩ L).card + (B.val ∩ H).card = 5 := by
    have heL : B.val ∩ L = B.val.filter fun p => degree C p = 3 := by
      ext p
      simp [L]
    have heH : B.val ∩ H = B.val.filter fun p => degree C p ≠ 3 := by
      ext p
      simp [H, hnot]
    rw [heL, heH, card_filter_add_card_filter_not, h.1 B.val B.property]
  have hpositive (B : C) : 1 ≤ (B.val ∩ H).card := by
    have hex : ∃ p ∈ B.val, degree C p ≠ 3 := by
      by_contra hh
      apply hno
      refine ⟨B.val, B.property, ?_⟩
      intro p hp
      by_contra hd
      exact hh ⟨p, hp, hd⟩
    obtain ⟨p, hp, hd⟩ := hex
    apply card_pos.mpr
    exact ⟨p, mem_inter.mpr ⟨hp, mem_filter.mpr ⟨mem_univ p, (hnot p).mp hd⟩⟩⟩
  have hpair (B : C) : ((B.val ∩ L).card).choose 2 + 3 * (B.val ∩ H).card = 9 := by
    have hp := hpositive B
    have hl : (B.val ∩ H).card ≤ 2 := by
      exact (card_le_card inter_subset_right).trans_eq hH
    have hs := hparts B
    have hc : (B.val ∩ H).card = 1 ∨ (B.val ∩ H).card = 2 := by omega
    rcases hc with hc | hc
    · have he : (B.val ∩ L).card = 4 := by omega
      rw [he, hc]
      decide
    · have he : (B.val ∩ L).card = 3 := by omega
      rw [he, hc]
      decide
  have hsum := sum_congr (s₁ := (univ : Finset C)) rfl (fun B _ => hpair B)
  rw [sum_add_distrib, ← mul_sum, hsumH] at hsum
  simp only [sum_const, card_univ, hv] at hsum
  have hconst : (7 • 9 : ℕ) = 63 := by decide
  rw [hconst] at hsum
  have hpairSum : (∑ B : C, ((B.val ∩ L).card).choose 2) = 39 := by omega
  have hb := ht L (fun p hp => (mem_filter.mp hp).2)
  rw [hL, hpairSum] at hb
  have hc : Nat.choose 9 2 = 36 := by decide
  rw [hc] at hb
  omega

omit [Fintype α] in
/-- Apply the indexed-triples inequality to any selected degree-three points.
Different points may have equal incidence triples; the indices retain their multiplicity. -/
theorem structural_triples_inequality {C : Family α} (h : IsCover C 5 2)
    (hC : C.card = 7) (L : Finset α) (hL : ∀ p ∈ L, degree C p = 3) :
    L.card.choose 2 + 2 * L.card ≤ (∑ B : C, ((B.val ∩ L).card).choose 2) + 14 := by
  let S : L → Finset C := fun p => structural_incidentRows C p.val
  have hv : Fintype.card C = 7 := by simpa using hC
  have hsize (p : L) : (S p).card = 3 := by
    exact (structural_incidentRows_card C p.val).trans (hL p.val p.property)
  have hmeet (p q : L) (hpq : p ≠ q) : (S p ∩ S q).Nonempty := by
    apply structural_incidentRows_meet h
    intro he
    exact hpq (Subtype.ext he)
  have hrow (B : C) : indexedDegree S B = (B.val ∩ L).card :=
    structural_indexed_row_card C L B
  have hb := intersecting_triples_bound S hv hsize hmeet
  simpa only [Fintype.card_coe, hrow] using hb

/-- Every point of a seven-block covering has degree at most four. -/
theorem structural_degree_bound {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7) (p : α) :
    degree C p ≤ 4 :=
  degree_bound_of_triples_inequality hn h hC (structural_triples_inequality h hC) p

theorem structural_degree_three_or_four {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7) (p : α) :
    degree C p = 3 ∨ degree C p = 4 := by
  have hl := degree_at_least_three_11_5_2 hn h p
  have hu := structural_degree_bound hn h hC p
  omega

/-- There are exactly two degree-four points. -/
theorem structural_degree_four_card {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7) :
    (univ.filter fun p => degree C p = 4).card = 2 :=
  degree_four_card_of_bound hn h hC (structural_degree_bound hn h hC)

/-- The other nine points have degree three. -/
theorem structural_degree_three_card {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7) :
    (univ.filter fun p => degree C p = 3).card = 9 :=
  degree_three_card_of_bound hn h hC (structural_degree_bound hn h hC)

/-- Some block consists entirely of degree-three points. -/
theorem structural_all_low_block {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7) :
    ∃ A ∈ C, ∀ p ∈ A, degree C p = 3 :=
  all_low_block_of_triples_inequality hn h hC (structural_degree_bound hn h hC)
    (structural_triples_inequality h hC)

#guard_standard_axioms structural_degree_bound structural_degree_four_card
  structural_degree_three_card structural_all_low_block

end CoveringDesigns
