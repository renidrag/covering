import CoveringDesigns.C12_6_3.Structural.Templates
import CoveringDesigns.Foundations.StandardAxioms

/-!
The two alternatives in GPPT Theorem 5.9 are disjoint. Every point of a
Figure 1 completion has degree at most nine, whereas Figure 6 has a point
of degree ten. This argument does not use the enumeration of completions.
-/

namespace CoveringDesigns.GPPTStructural

open Finset

theorem core_degree (p : Fin 12) : degree core p = 6 := by
  exact (show ∀ p : Fin 12, degree core p = 6 by decide +kernel) p

/-- Adding three blocks raises the degree of a point by at most three. -/
theorem templateBlocks_degree_le_nine (R : Fin 3 → Finset (Fin 12))
    (p : Fin 12) : degree (templateBlocks R) p ≤ 9 := by
  let E := univ.image (fun i => spine i ∪ R i)
  have hE : E.card ≤ 3 := by
    exact (card_image_le).trans_eq (show (univ : Finset (Fin 3)).card = 3 by rfl)
  have hs : (E.filter (p ∈ ·)).card ≤ E.card := card_le_card (filter_subset _ _)
  have hu := card_union_le (core.filter (p ∈ ·)) (E.filter (p ∈ ·))
  have hcore : (core.filter (p ∈ ·)).card = 6 := core_degree p
  change ((core ∪ E).filter (p ∈ ·)).card ≤ 9
  rw [filter_union]
  omega

theorem templateCompletion_degree_le_nine {C : Family (Fin 12)}
    (hC : IsTemplateCompletion C) (p : Fin 12) : degree C p ≤ 9 := by
  obtain ⟨R, _, rfl⟩ := hC
  exact templateBlocks_degree_le_nine R p

theorem IsomorphicTemplateCompletion.degree_le_nine {C : Family (Fin 12)}
    (hC : IsomorphicTemplateCompletion C) (p : Fin 12) : degree C p ≤ 9 := by
  obtain ⟨D, hD, e, he⟩ := hC
  have h := templateCompletion_degree_le_nine hD (e p)
  rw [← he, degree_relabel] at h
  exact h

theorem figure6_degree_four : degree figure6 (4 : Fin 12) = 10 := by decide +kernel

theorem IsomorphicTemplateCompletion.not_isomorphic_figure6 {C : Family (Fin 12)}
    (hC : IsomorphicTemplateCompletion C) : ¬ Isomorphic C figure6 := by
  rintro ⟨e, he⟩
  have hb := hC.degree_le_nine (e.symm 4)
  have hd := degree_relabel e C (e.symm 4)
  rw [he, e.apply_symm_apply, figure6_degree_four] at hd
  omega

#guard_standard_axioms core_degree templateBlocks_degree_le_nine
  templateCompletion_degree_le_nine IsomorphicTemplateCompletion.degree_le_nine
  figure6_degree_four IsomorphicTemplateCompletion.not_isomorphic_figure6

end CoveringDesigns.GPPTStructural
