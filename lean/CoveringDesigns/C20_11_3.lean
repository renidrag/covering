import CoveringDesigns.C20_11_3.LowerBound
import CoveringDesigns.C20_11_3.Witness
import CoveringDesigns.Foundations.StandardAxioms

/-!
C(20,11,3) = 12: elementary incidence, a boundary-rank obstruction and
shared-block counting give the lower bound; the historical twelve-block
witness gives attainment. Research and formalisation by Rob Gardiner with
AI assistance. No claim of a new construction or historical priority.
-/

namespace CoveringDesigns

/-- Exactness, including an actual attaining family, on arbitrary labels. -/
theorem covering_number_20_11_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20) :
    (∃ C : Family α, IsCover C 11 3 ∧ C.card = 12) ∧
    (∀ C : Family α, IsCover C 11 3 → 12 ≤ C.card) :=
  ⟨upper_bound_20_11_3_on hv, fun _ hC => lower_bound_20_11_3 hv hC⟩

/-- The project's usual exact covering-number interface. -/
theorem covering_number_20_11_3 :
    (∃ C : Family (Fin 20), IsCover C 11 3 ∧ C.card = 12) ∧
    (∀ C : Family (Fin 20), IsCover C 11 3 → 12 ≤ C.card) :=
  covering_number_20_11_3_on (by simp)

#guard_standard_axioms lower_bound_20_11_3 upper_bound_20_11_3_on
  covering_number_20_11_3_on covering_number_20_11_3

#print axioms covering_number_20_11_3

end CoveringDesigns
