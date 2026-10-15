import CoveringDesigns.C11_5_2.StantonConsequences
import CoveringDesigns.Foundations.StarRelabelling
import CoveringDesigns.Foundations.StandardAxioms

/-!
The value and the two isomorphism types of minimum (11,5,2) coverings.
The explicit representatives are checked in the kernel.  The completeness
theorem imported above is separate from these witness and separation proofs.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns

open Finset

theorem stanton_representative_card (tag : Bool) :
    (stantonRepresentative tag).card = 7 := by
  cases tag <;> decide +kernel

section
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem stanton_representative_isCover (tag : Bool) :
    IsCover (stantonRepresentative tag) 5 2 := by
  constructor
  · cases tag <;> unfold Uniform stantonRepresentative <;> decide +kernel
  · apply covers_of_powersetCard
    cases tag <;> unfold stantonRepresentative <;> decide +kernel

private def hasTwoTripleNeighbors {α : Type*} [DecidableEq α]
    (C : Family α) : Prop :=
  ∃ A ∈ C, ∃ B ∈ C, ∃ D ∈ C,
    A ≠ B ∧ A ≠ D ∧ B ≠ D ∧ (A ∩ B).card = 3 ∧ (A ∩ D).card = 3

private theorem stanton_false_separation :
    ¬ hasTwoTripleNeighbors (stantonRepresentative false) := by
  unfold hasTwoTripleNeighbors stantonRepresentative
  decide +kernel

private theorem stanton_true_separation :
    hasTwoTripleNeighbors (stantonRepresentative true) := by
  refine ⟨{0, 4, 8, 9, 10}, ?_, {0, 1, 4, 5, 8}, ?_,
    {0, 2, 4, 6, 9}, ?_, ?_⟩ <;> decide +kernel

end

private theorem hasTwoTripleNeighbors_relabel {α β : Type*}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) {C : Family α}
    (h : hasTwoTripleNeighbors C) : hasTwoTripleNeighbors (relabel e C) := by
  obtain ⟨A, hA, B, hB, D, hD, hAB, hAD, hBD, h3B, h3D⟩ := h
  refine ⟨A.map e.toEmbedding, (mem_relabel e C A).mpr hA,
    B.map e.toEmbedding, (mem_relabel e C B).mpr hB,
    D.map e.toEmbedding, (mem_relabel e C D).mpr hD,
    (fun h => hAB (map_inj.mp h)), (fun h => hAD (map_inj.mp h)),
    (fun h => hBD (map_inj.mp h)), ?_, ?_⟩
  · simpa only [← map_inter, card_map] using h3B
  · simpa only [← map_inter, card_map] using h3D

/-- One representative has a block meeting two other blocks in three points;
the other does not.  Hence they are not isomorphic. -/
theorem stanton_representatives_not_isomorphic :
    ¬ Isomorphic (stantonRepresentative false) (stantonRepresentative true) := by
  rintro ⟨e, he⟩
  have h := hasTwoTripleNeighbors_relabel e.symm stanton_true_separation
  rw [← he, relabel_symm_relabel] at h
  exact stanton_false_separation h

/-- The catalogue has no duplicate isomorphism types. -/
theorem stanton_representatives_isomorphic_iff (s t : Bool) :
    Isomorphic (stantonRepresentative s) (stantonRepresentative t) ↔ s = t := by
  constructor
  · intro h
    cases s <;> cases t
    · rfl
    · exact (stanton_representatives_not_isomorphic h).elim
    · obtain ⟨e, he⟩ := h
      apply False.elim
      apply stanton_representatives_not_isomorphic
      exact ⟨e.symm, by rw [← he, relabel_symm_relabel]⟩
    · rfl
  · rintro rfl
    exact ⟨Equiv.refl _, relabel_refl _⟩

/-- Every minimum covering has exactly one of the two isomorphism types. -/
theorem stanton_classification_unique_on {α : Type*} [Fintype α] [DecidableEq α]
    (hn : Fintype.card α = 11) {C : Family α}
    (hC : IsCover C 5 2) (hb : C.card = 7) :
    ∃! tag, Isomorphic C (stantonRepresentative tag) := by
  obtain ⟨tag, htag⟩ := stanton_classification_on hn hC hb
  refine ⟨tag, htag, ?_⟩
  intro other hother
  obtain ⟨e, he⟩ := hother
  have hi : Isomorphic (stantonRepresentative other) C :=
    ⟨e.symm, by rw [← he, relabel_symm_relabel]⟩
  exact (stanton_representatives_isomorphic_iff other tag).mp (hi.trans htag)

/-- The equality C(11,5,2)=7, expressed by a witness and a universal bound. -/
theorem covering_number_11_5_2 :
    (∃ C : Family (Fin 11), IsCover C 5 2 ∧ C.card = 7) ∧
    (∀ C : Family (Fin 11), IsCover C 5 2 → 7 ≤ C.card) :=
  ⟨⟨stantonRepresentative false, stanton_representative_isCover false,
      stanton_representative_card false⟩,
    fun _ hC => lower_bound_11_5_2 (by simp) hC⟩

#guard_standard_axioms stanton_representative_card stanton_representative_isCover
  stanton_representatives_not_isomorphic stanton_representatives_isomorphic_iff
  covering_number_11_5_2
  stanton_classification stanton_classification_on stanton_classification_unique_on
  stanton_degree_bound stanton_degree_bound_on
  stanton_intersection_bound stanton_intersection_bound_on

end CoveringDesigns
