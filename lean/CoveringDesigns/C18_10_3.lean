import CoveringDesigns.C18_10_3.LowerBound
import CoveringDesigns.C18_10_3.Witness
import CoveringDesigns.Foundations.StandardAxioms

/-! C(18,10,3)=12: unconditional lower exclusion and the historical upper witness.
Research and formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns

/-- Arbitrary-label exactness, including an actual attaining family. -/
theorem covering_number_18_10_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 18) :
    (∃ C : Family α, IsCover C 10 3 ∧ C.card = 12) ∧
    (∀ C : Family α, IsCover C 10 3 → 12 ≤ C.card) := by
  classical
  exact ⟨upper_bound_18_10_3_on hv,fun _ hC => lower_bound_18_10_3 hv hC⟩

theorem covering_number_18_10_3 :
    (∃ C : Family (Fin 18), IsCover C 10 3 ∧ C.card = 12) ∧
    (∀ C : Family (Fin 18), IsCover C 10 3 → 12 ≤ C.card) :=
  covering_number_18_10_3_on (by simp)

#guard_standard_axioms lower_bound_18_10_3 upper_bound_18_10_3_on
  covering_number_18_10_3_on covering_number_18_10_3
#print axioms covering_number_18_10_3

end CoveringDesigns
