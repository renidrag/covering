import CoveringDesigns.C34_18_3.LowerBound
import CoveringDesigns.C34_18_3.Witness
import CoveringDesigns.Foundations.StandardAxioms

/-! C(34,18,3)=13: the existing unconditional lower theorem and the historical
LJCR attaining family. No new construction or historical priority is claimed.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns

/-- Exactness with actual attainment on arbitrary finite labels. -/
theorem covering_number_34_18_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 34) :
    (∃ C : Family α, IsCover C 18 3 ∧ C.card = 13) ∧
    (∀ C : Family α, IsCover C 18 3 → 13 ≤ C.card) := by
  classical
  exact ⟨upper_bound_34_18_3_on hv, fun _ hC => lower_bound_34_18_3 hv hC⟩

/-- Exactness on the canonical finite point type. -/
theorem covering_number_34_18_3 :
    (∃ C : Family (Fin 34), IsCover C 18 3 ∧ C.card = 13) ∧
    (∀ C : Family (Fin 34), IsCover C 18 3 → 13 ≤ C.card) :=
  covering_number_34_18_3_on (by simp)

#guard_standard_axioms lower_bound_34_18_3 upper_bound_34_18_3_on
  covering_number_34_18_3_on covering_number_34_18_3

end CoveringDesigns
