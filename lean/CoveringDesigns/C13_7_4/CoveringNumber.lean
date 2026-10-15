import CoveringDesigns.C13_7_4.Structural.CoveringNumber

/-! Public statements of the structural thirteen-point result. -/

namespace CoveringDesigns

/-- Every covering of the four-subsets of thirteen points by seven-subsets
has at least thirty blocks. -/
theorem lower_bound_30 {C : Family (Fin 13)} (hC : IsCover C 7 4) : 30 ≤ C.card :=
  C13Structural.lower_bound_30 (by simp) hC

/-- C(13,7,4)=30: an explicit witness and an unconditional universal lower bound. -/
theorem covering_number_13_7_4 :
    (∃ C : Family (Fin 13), IsCover C 7 4 ∧ C.card = 30) ∧
    (∀ C : Family (Fin 13), IsCover C 7 4 → 30 ≤ C.card) :=
  C13Structural.covering_number_13_7_4

#guard_standard_axioms lower_bound_30 covering_number_13_7_4

end CoveringDesigns
