import CoveringDesigns.C19_9_3.LowerBound
import CoveringDesigns.C19_9_3.Witness

/-! C(19,9,3)=17. Belic's historical construction supplies attainment;
actual minimum-link compatibility supplies the independent lower bound. -/
namespace CoveringDesigns

/-- Exact covering number on every finite nineteen-point type. -/
theorem covering_number_19_9_3_on {V : Type*} [Fintype V] [DecidableEq V]
    (hv : Fintype.card V = 19) :
    (∃ C : Family V, IsCover C 9 3 ∧ C.card = 17) ∧
      (∀ C : Family V, IsCover C 9 3 → 17 ≤ C.card) :=
  ⟨upper_bound_19_9_3_on hv,fun _ h => lower_bound_19_9_3_on hv h⟩

/-- C(19,9,3)=17 in the project's attainment-plus-universal-lower convention. -/
theorem covering_number_19_9_3 :
    (∃ C : Family (Fin 19), IsCover C 9 3 ∧ C.card = 17) ∧
      (∀ C : Family (Fin 19), IsCover C 9 3 → 17 ≤ C.card) :=
  covering_number_19_9_3_on (by simp)

/-- Fully expanded ordinary-family exactness on arbitrary nineteen-point
types. The attaining family is the transported historical Belic witness. -/
theorem covering_number_19_9_3_expanded_on {V : Type*} [Fintype V] [DecidableEq V]
    (hv : Fintype.card V = 19) :
    (∃ C : Finset (Finset V), C.card = 17 ∧ (∀ B ∈ C, B.card = 9) ∧
      (∀ T : Finset V, T.card = 3 → ∃ B ∈ C, T ⊆ B)) ∧
    (∀ C : Finset (Finset V), (∀ B ∈ C, B.card = 9) →
      (∀ T : Finset V, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 17 ≤ C.card) := by
  refine ⟨⟨knownCover17_19_9_3_on hv,knownCover17_19_9_3_on_card hv,
    (knownCover17_19_9_3_on_isCover hv).1,(knownCover17_19_9_3_on_isCover hv).2⟩,?_⟩
  exact fun C hu hc => lower_bound_19_9_3_expanded hv C hu hc

#guard_standard_axioms covering_number_19_9_3_on covering_number_19_9_3 covering_number_19_9_3_expanded_on
end CoveringDesigns
