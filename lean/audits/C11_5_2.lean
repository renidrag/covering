import CoveringDesigns.C11_5_2

/-! Standalone audit: this import has no dependency on either larger covering. -/

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.Isomorphic

#check (CoveringDesigns.stanton_classification :
  ∀ {C : Finset (Finset (Fin 11))}, CoveringDesigns.IsCover C 5 2 → C.card = 7 →
    ∃ tag : Bool, CoveringDesigns.Isomorphic C (CoveringDesigns.stantonRepresentative tag))

#check (CoveringDesigns.stanton_classification_unique_on (α := Fin 11) (by simp) :
  ∀ {C : Finset (Finset (Fin 11))}, CoveringDesigns.IsCover C 5 2 → C.card = 7 →
    ∃! tag : Bool, CoveringDesigns.Isomorphic C (CoveringDesigns.stantonRepresentative tag))

namespace CoveringDesigns.Audit11

/-- The covering-number statement expressed directly in finite sets. -/
theorem covering_number_explicit :
    (∃ C : Finset (Finset (Fin 11)),
      (∀ B ∈ C, B.card = 5) ∧
      (∀ T : Finset (Fin 11), T.card = 2 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 7) ∧
    (∀ C : Finset (Finset (Fin 11)),
      (∀ B ∈ C, B.card = 5) →
      (∀ T : Finset (Fin 11), T.card = 2 → ∃ B ∈ C, T ⊆ B) → 7 ≤ C.card) := by
  constructor
  · obtain ⟨C, hC, hcard⟩ := CoveringDesigns.covering_number_11_5_2.1
    exact ⟨C, hC.1, hC.2, hcard⟩
  · intro C hu hc
    exact CoveringDesigns.covering_number_11_5_2.2 C ⟨hu, hc⟩

/-- Every seven-block covering belongs to exactly one catalogue type.
Its only hypotheses are block size, coverage, and the number of blocks. -/
theorem classification_explicit :
    ∀ C : Finset (Finset (Fin 11)),
      (∀ B ∈ C, B.card = 5) →
      (∀ T : Finset (Fin 11), T.card = 2 → ∃ B ∈ C, T ⊆ B) → C.card = 7 →
      ∃! tag : Bool, ∃ e : Fin 11 ≃ Fin 11,
        C.map (Finset.mapEmbedding e.toEmbedding).toEmbedding =
          CoveringDesigns.stantonRepresentative tag := by
  intro C hu hc hcard
  exact CoveringDesigns.stanton_classification_unique_on (by simp) ⟨hu, hc⟩ hcard

end CoveringDesigns.Audit11

#guard_standard_axioms CoveringDesigns.lower_bound_11_5_2
  CoveringDesigns.stanton_representative_card CoveringDesigns.stanton_representative_isCover
  CoveringDesigns.stanton_representatives_not_isomorphic
  CoveringDesigns.stanton_representatives_isomorphic_iff
  CoveringDesigns.covering_number_11_5_2 CoveringDesigns.Audit11.covering_number_explicit

#print axioms CoveringDesigns.lower_bound_11_5_2
#print axioms CoveringDesigns.stanton_classification
#print axioms CoveringDesigns.stanton_classification_unique_on
#print axioms CoveringDesigns.covering_number_11_5_2
#print axioms CoveringDesigns.Audit11.covering_number_explicit
#print axioms CoveringDesigns.Audit11.classification_explicit

#guard_standard_axioms CoveringDesigns.stanton_classification
  CoveringDesigns.stanton_classification_on
  CoveringDesigns.stanton_classification_unique_on
  CoveringDesigns.stanton_degree_bound CoveringDesigns.stanton_degree_bound_on
  CoveringDesigns.stanton_intersection_bound CoveringDesigns.stanton_intersection_bound_on
  CoveringDesigns.Audit11.classification_explicit
  CoveringDesigns.StantonStructural.template_classification
  CoveringDesigns.StantonStructural.exists_six_block_frame

#print axioms CoveringDesigns.stanton_representative_isCover
#print axioms CoveringDesigns.stanton_representatives_not_isomorphic
#print axioms CoveringDesigns.StantonStructural.template_classification
#print axioms CoveringDesigns.StantonStructural.exists_six_block_frame

#guard_standard_axioms CoveringDesigns.stanton_partition_on
  CoveringDesigns.stanton_template_on
  CoveringDesigns.StantonStructural.SixBlockFrame.nonempty_templatePartition
#print axioms CoveringDesigns.stanton_partition_on
#print axioms CoveringDesigns.stanton_template_on
#print axioms CoveringDesigns.StantonStructural.SixBlockFrame.nonempty_templatePartition
