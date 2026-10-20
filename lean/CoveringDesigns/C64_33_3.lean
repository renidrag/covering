import CoveringDesigns.C64_33_3.Bounds
import CoveringDesigns.Foundations.StandardAxioms

namespace CoveringDesigns

theorem covering_number_64_33_3 :
    (∃ C : Family (Fin 64), IsCover C 33 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin 64), IsCover C 33 3 → 14 ≤ C.card) :=
  C64_33_3.exactness_on (by simp)

#guard_standard_axioms C64_33_3.exactness_on covering_number_64_33_3
end CoveringDesigns
