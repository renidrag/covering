import CoveringDesigns.C13_7_4.Structural.Basic
import CoveringDesigns.C13_7_4.Structural.GPPTGeometry

/-! Structural degree bounds and ordinary-link extraction for a high pair. -/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every pair lies in at least seven blocks, by the eleven-point lower bound. -/
theorem pair_degree_lower {C : Family α} (hn : Fintype.card α = 13)
    (hC : IsCover C 7 4) {p q : α} (hpq : p ≠ q) :
    7 ≤ degree (star C p) q := by
  have h := degree_at_least_seven_12_6_3
    (by rw [complement_point_card, hn]) (link_isCover hC p)
    (⟨q, hpq.symm⟩ : {x : α // x ≠ p})
  rwa [degree_link] at h

/-- A pair through a minimum point has multiplicity at most ten. -/
theorem minimum_pair_degree_upper {C : Family α} (hn : Fintype.card α = 13)
    (hC : IsCover C 7 4) {p q : α} (hp : degree C p = 15) (hpq : p ≠ q) :
    degree (star C p) q ≤ 10 := by
  have h := minimum_degree_le_ten
    (by rw [complement_point_card, hn]) (link_isCover hC p)
    (by rw [link_card, hp]) (⟨q, hpq.symm⟩ : {x : α // x ≠ p})
  rwa [degree_link] at h

/-- These are the only possible multiplicities before the compatibility exclusions. -/
theorem minimum_pair_options {C : Family α} (hn : Fintype.card α = 13)
    (hC : IsCover C 7 4) {p q : α} (hp : degree C p = 15) (hpq : p ≠ q) :
    degree (star C p) q = 7 ∨ degree (star C p) q = 8 ∨
      degree (star C p) q = 9 ∨ degree (star C p) q = 10 := by
  have := pair_degree_lower hn hC hpq
  have := minimum_pair_degree_upper hn hC hp hpq
  omega

/-- A minimum link with a point of degree eight or nine must be ordinary.
The conclusion retains an actual template isomorphism, not just incidence
consequences of that isomorphism. -/
theorem ordinary_link_of_pair_eight_or_nine {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) {p q : α}
    (hp : degree C p = 15) (hpq : p ≠ q)
    (hpqdegree : degree (star C p) q = 8 ∨ degree (star C p) q = 9) :
    ∃ D : Family (Fin 12), IsTemplateCompletion D ∧ Isomorphic (link C p) D := by
  let e : {x : α // x ≠ p} ≃ Fin 12 :=
    Fintype.equivFinOfCardEq (by rw [complement_point_card, hn])
  have hcover := relabel_isCover e (link_isCover hC p)
  have hcard : (relabel e (link C p)).card = 15 := by
    rw [relabel_card, link_card, hp]
  rcases gppt_structural_reduction hcover hcard with h | h
  · obtain ⟨D, hD, he⟩ := h
    exact ⟨D, hD, Isomorphic.trans ⟨e, rfl⟩ he⟩
  · obtain ⟨G⟩ := exceptional_geometry_of_isomorphic (Isomorphic.trans ⟨e, rfl⟩ h)
    let q' : {x : α // x ≠ p} := ⟨q, hpq.symm⟩
    have hd : degree (link C p) q' = 7 ∨ degree (link C p) q' = 10 := by
      by_cases hq : q' ∈ G.high
      · exact Or.inr (G.degree_high q' hq)
      · exact Or.inl (G.degree_low q' hq)
    simp only [degree_link] at hd
    dsimp only [q'] at hd
    exfalso
    omega

/-- No four-point set can contain all minimum points of a small covering. -/
theorem minima_not_confined {C : Family α} (hn : Fintype.card α = 13)
    (hC : IsCover C 7 4) (hb : C.card ≤ 29) {S : Finset α} (hs : S.card ≤ 4)
    (hsub : minimumPoints C 15 ⊆ S) : False := by
  have hlo := five_minimum_points hn hC hb
  have hhi := card_le_card hsub
  omega

#guard_standard_axioms pair_degree_lower minimum_pair_degree_upper
  minimum_pair_options ordinary_link_of_pair_eight_or_nine minima_not_confined

end CoveringDesigns.C13Structural
