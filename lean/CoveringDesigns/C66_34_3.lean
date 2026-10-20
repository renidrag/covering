import CoveringDesigns.C66_34_3.Bounds
import CoveringDesigns.Foundations.StandardAxioms

namespace CoveringDesigns

theorem covering_number_66_34_3 :
    (∃ C : Family (Fin 66), IsCover C 34 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin 66), IsCover C 34 3 → 14 ≤ C.card) :=
  C66_34_3.exactness_on (by simp)

#guard_standard_axioms C66_34_3.exactness_on covering_number_66_34_3
end CoveringDesigns
