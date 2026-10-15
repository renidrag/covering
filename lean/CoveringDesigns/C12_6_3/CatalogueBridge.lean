import CoveringDesigns.C12_6_3.Catalogue
import CoveringDesigns.C12_6_3.Structural.Exceptional
import CoveringDesigns.C12_6_3.Structural.Separation

/-!
Catalogue-facing forms of the structural Figure 6 results.
The structural reduction uses Figure 6 directly; the classification layer
identifies it with the catalogue's final entry through this module.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace CoveringDesigns.GPPTStructural

/-- The exceptional family is literally the last entry of the retained catalogue. -/
theorem figure6_eq_exceptional : figure6 = linkRepresentative 67 := by
  decide +kernel

theorem figure6_isomorphic_exceptional : Isomorphic figure6 (linkRepresentative 67) := by
  refine ⟨Equiv.refl _, ?_⟩
  simpa only [relabel_refl] using figure6_eq_exceptional

namespace TriplicateFrame

variable {α : Type*} [DecidableEq α] [Fintype α] {C : Family α}

/-- Case 2 in the retained catalogue's exceptional-representative notation. -/
theorem common_column_isomorphic_exceptional (F : TriplicateFrame C)
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hc : C.card = 15)
    {x : α} {j : Fin 3} (hx : x ∈ F.common.triad j)
    (hsel : ∀ r, (F.row r).selected j = x) : Isomorphic C (linkRepresentative 67) := by
  rw [← figure6_eq_exceptional]
  exact F.common_column_isomorphic_figure6 hn hC hc hx hsel

end TriplicateFrame

theorem IsomorphicTemplateCompletion.not_isomorphic_exceptional {C : Family (Fin 12)}
    (hC : IsomorphicTemplateCompletion C) : ¬ Isomorphic C (linkRepresentative 67) := by
  rw [← figure6_eq_exceptional]
  exact hC.not_isomorphic_figure6

#guard_standard_axioms figure6_eq_exceptional figure6_isomorphic_exceptional
  TriplicateFrame.common_column_isomorphic_exceptional
  IsomorphicTemplateCompletion.not_isomorphic_exceptional

#print axioms figure6_eq_exceptional

end CoveringDesigns.GPPTStructural
