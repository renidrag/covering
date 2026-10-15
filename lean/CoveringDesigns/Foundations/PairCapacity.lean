import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.Omega

/-!
A direct capacity obstruction for pairs crossing between two disjoint sets.
A set of at most four points covers at most four such ordered pairs. Hence two
such sets cannot cover the nine pairs between two disjoint triples.
-/

namespace CoveringDesigns

open Finset

variable {α : Type*} [DecidableEq α]

/-- If two nonnegative integers have sum at most four, their product is at most
four. The five arithmetic cases concern one cardinality, not configurations. -/
theorem mul_le_four_of_add_le_four {a b : ℕ} (h : a + b ≤ 4) : a * b ≤ 4 := by
  have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega

/-- The parts of a four-point set on two disjoint sides have product at most
four, regardless of points of the set outside those sides. -/
theorem disjoint_crossparts_card_mul_le_four (T W U : Finset α)
    (hTW : Disjoint T W) (hU : U.card ≤ 4) :
    (T ∩ U).card * (W ∩ U).card ≤ 4 := by
  have hd : Disjoint (T ∩ U) (W ∩ U) :=
    hTW.mono inter_subset_left inter_subset_left
  have hs : (T ∩ U) ∪ (W ∩ U) ⊆ U :=
    union_subset inter_subset_right inter_subset_right
  apply mul_le_four_of_add_le_four
  rw [← card_union_of_disjoint hd]
  exact (card_le_card hs).trans hU

/-- A four-point set covers at most four ordered pairs crossing disjoint sides. -/
theorem cross_pairs_card_le_four (T W U : Finset α)
    (hTW : Disjoint T W) (hU : U.card ≤ 4) :
    ((T ∩ U) ×ˢ (W ∩ U)).card ≤ 4 := by
  rw [card_product]
  exact disjoint_crossparts_card_mul_le_four T W U hTW hU

/-- Coverage by two sets bounds the number of cross pairs by the sum of their
individual capacities. No disjointness assumption is needed for this bound. -/
theorem cross_pairs_card_le_two_capacities (T W U V : Finset α)
    (hcover : ∀ x ∈ T, ∀ y ∈ W,
      (x ∈ U ∧ y ∈ U) ∨ (x ∈ V ∧ y ∈ V)) :
    T.card * W.card ≤
      (T ∩ U).card * (W ∩ U).card + (T ∩ V).card * (W ∩ V).card := by
  have hs : T ×ˢ W ⊆ ((T ∩ U) ×ˢ (W ∩ U)) ∪ ((T ∩ V) ×ˢ (W ∩ V)) := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    rcases hcover x hx y hy with hU | hV
    · apply mem_union_left
      exact mem_product.mpr ⟨mem_inter.mpr ⟨hx, hU.1⟩, mem_inter.mpr ⟨hy, hU.2⟩⟩
    · apply mem_union_right
      exact mem_product.mpr ⟨mem_inter.mpr ⟨hx, hV.1⟩, mem_inter.mpr ⟨hy, hV.2⟩⟩
  have hc := (card_le_card hs).trans (card_union_le _ _)
  simpa only [card_product] using hc

/-- Two sets of at most four points cannot cover all nine ordered pairs between
two disjoint triples: their combined capacity is at most `4 + 4 < 9`. -/
theorem two_four_sets_not_cover_three_by_three (T W U V : Finset α)
    (hTW : Disjoint T W) (hT : T.card = 3) (hW : W.card = 3)
    (hU : U.card ≤ 4) (hV : V.card ≤ 4) :
    ¬ (∀ x ∈ T, ∀ y ∈ W,
      (x ∈ U ∧ y ∈ U) ∨ (x ∈ V ∧ y ∈ V)) := by
  intro hcover
  have hc := cross_pairs_card_le_two_capacities T W U V hcover
  have hu := disjoint_crossparts_card_mul_le_four T W U hTW hU
  have hv := disjoint_crossparts_card_mul_le_four T W V hTW hV
  rw [hT, hW] at hc
  omega

#guard_standard_axioms mul_le_four_of_add_le_four
  disjoint_crossparts_card_mul_le_four cross_pairs_card_le_four
  cross_pairs_card_le_two_capacities two_four_sets_not_cover_three_by_three

#print axioms two_four_sets_not_cover_three_by_three

end CoveringDesigns
