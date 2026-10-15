import CoveringDesigns.C12_6_3.Structural.Branching
import CoveringDesigns.C12_6_3.Structural.ProjectiveCover
import CoveringDesigns.C12_6_3.Structural.TriplicateClassification
import CoveringDesigns.C12_6_3.Structural.Separation

/-! The structural classification part of GPPT Theorem 5.9.
This theorem precedes the finite enumeration of Figure 1 completions.
It does not assert the paper's separate element-minimality conclusions. -/

namespace CoveringDesigns

open GPPTStructural

/-- Every minimum covering has the Figure 1 completion shape or is Figure 6.
The proof splits only on repetition of a triple of minimum-degree points. -/
theorem gppt_structural_reduction {C : Family (Fin 12)}
    (hC : IsCover C 6 3) (hb : C.card = 15) :
    IsomorphicTemplateCompletion C ∨ Isomorphic C figure6 := by
  by_cases hno : NoDuplicateMinimumTriple C
  · exact Or.inl (GPPTProjective.no_duplicate_isomorphicTemplateCompletion hC hb hno)
  · obtain ⟨F⟩ := triplicate_frame_of_not_noDuplicate (by simp) hC hb.le hno
    exact F.classification hC hb

/-- The two alternatives in the structural reduction are disjoint. -/
theorem gppt_structural_alternatives_disjoint (C : Family (Fin 12)) :
    ¬ (IsomorphicTemplateCompletion C ∧ Isomorphic C figure6) := by
  rintro ⟨ht, he⟩
  exact ht.not_isomorphic_figure6 he

#guard_standard_axioms gppt_structural_reduction gppt_structural_alternatives_disjoint

end CoveringDesigns
