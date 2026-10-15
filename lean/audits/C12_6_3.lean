import CoveringDesigns.C12_6_3

/-! Standalone audit: this import has no dependency on the thirteen-point proof. -/

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.Isomorphic
#print CoveringDesigns.GPPTStructural.ValidAdditions
#print CoveringDesigns.GPPTStructural.IsTemplateCompletion
#print CoveringDesigns.GPPTStructural.IsomorphicTemplateCompletion

#check (CoveringDesigns.gppt_structural_reduction :
  ∀ {C : Finset (Finset (Fin 12))}, CoveringDesigns.IsCover C 6 3 → C.card = 15 →
    CoveringDesigns.GPPTStructural.IsomorphicTemplateCompletion C ∨
      CoveringDesigns.Isomorphic C CoveringDesigns.figure6)

#check (CoveringDesigns.gppt_structural_alternatives_disjoint :
  ∀ C : Finset (Finset (Fin 12)),
    ¬ (CoveringDesigns.GPPTStructural.IsomorphicTemplateCompletion C ∧
      CoveringDesigns.Isomorphic C CoveringDesigns.figure6))

#check (CoveringDesigns.gppt_classification :
  ∀ {C : Finset (Finset (Fin 12))}, CoveringDesigns.IsCover C 6 3 → C.card ≤ 15 →
    C.card = 15 ∧ ∃ i : Fin 68, CoveringDesigns.Isomorphic C (CoveringDesigns.linkRepresentative i))

namespace CoveringDesigns.Audit12

/-- The covering-number statement expressed directly in finite sets. -/
theorem covering_number_explicit :
    (∃ C : Finset (Finset (Fin 12)),
      (∀ B ∈ C, B.card = 6) ∧
      (∀ T : Finset (Fin 12), T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 15) ∧
    (∀ C : Finset (Finset (Fin 12)),
      (∀ B ∈ C, B.card = 6) →
      (∀ T : Finset (Fin 12), T.card = 3 → ∃ B ∈ C, T ⊆ B) → 15 ≤ C.card) := by
  constructor
  · obtain ⟨C, hC, hcard⟩ := CoveringDesigns.covering_number_12_6_3.1
    exact ⟨C, hC.1, hC.2, hcard⟩
  · intro C hu hc
    exact CoveringDesigns.covering_number_12_6_3.2 C ⟨hu, hc⟩

end CoveringDesigns.Audit12

#print axioms CoveringDesigns.stanton_classification
#print axioms CoveringDesigns.gppt_classification
#print axioms CoveringDesigns.covering_number_12_6_3
#print axioms CoveringDesigns.figure6_isCover
#print axioms CoveringDesigns.Audit12.covering_number_explicit

#print axioms CoveringDesigns.gppt_structural_reduction
#print axioms CoveringDesigns.GPPTStructural.template_classification
#print axioms CoveringDesigns.GPPTStructural.lower_bound_fifteen
#print axioms CoveringDesigns.GPPTProjective.no_duplicate_isomorphicTemplateCompletion

#guard_standard_axioms CoveringDesigns.gppt_classification
  CoveringDesigns.gppt_classification_on CoveringDesigns.lower_bound_12_6_3
  CoveringDesigns.covering_number_12_6_3 CoveringDesigns.Audit12.covering_number_explicit
  CoveringDesigns.gppt_structural_reduction
  CoveringDesigns.GPPTStructural.template_classification
