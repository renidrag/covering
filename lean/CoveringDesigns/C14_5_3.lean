import CoveringDesigns.C14_5_3.LowerBound
import CoveringDesigns.C14_5_3.Completion28
import CoveringDesigns.C14_5_3.Witness
import CoveringDesigns.Foundations.StandardAxioms

/-! The interval 41 ≤ C(14,5,3) ≤ 43, with an actual historical upper witness.
Research and formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns

/-- Unconditional ordinary lower bound on any fourteen-point type. -/
theorem lower_bound_14_5_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 14) (hC : IsCover C 5 3) : 41 ≤ C.card := by
  classical
  exact C14_5_3.lower_bound hv hC

/-- Occurrence-indexed contract, explicitly permitting repeated blocks. -/
theorem indexed_lower_bound_14_5_3 {α ι : Type*} [Fintype α] [Fintype ι]
    (B : ι → Finset α) (hv : Fintype.card α = 14)
    (hu : ∀ i, (B i).card = 5)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) : 41 ≤ Fintype.card ι := by
  classical
  exact C14_5_3.indexed_lower_bound hv ⟨hu,(Multicover.covers_one_iff B 3).mpr hc⟩

/-- The interval includes a 43-block witness; it makes no exactness claim. -/
theorem covering_interval_14_5_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 14) :
    (∀ C : Family α, IsCover C 5 3 → 41 ≤ C.card) ∧
      (∃ C : Family α, IsCover C 5 3 ∧ C.card = 43) := by
  classical
  exact ⟨fun _ hC => lower_bound_14_5_3 hv hC,upper_bound_14_5_3_on hv⟩

theorem covering_interval_14_5_3 :
    (∀ C : Family (Fin 14), IsCover C 5 3 → 41 ≤ C.card) ∧
      (∃ C : Family (Fin 14), IsCover C 5 3 ∧ C.card = 43) :=
  covering_interval_14_5_3_on (by simp)

#guard_standard_axioms lower_bound_14_5_3 indexed_lower_bound_14_5_3
  covering_interval_14_5_3_on covering_interval_14_5_3
#print axioms covering_interval_14_5_3

end CoveringDesigns
