import CoveringDesigns.C12_6_3.Structural.Reduction
import CoveringDesigns.C12_6_3.Structural.Completions
import CoveringDesigns.C12_6_3.CatalogueBridge

/-! GPPT catalogue completeness from the structural Figure 1/Figure 6
reduction and kernel-checked completion witnesses. The standalone Stanton
classification is proved in this project. No native assertions are used. -/

namespace CoveringDesigns

/-- Every (12,6,3) covering with at most fifteen blocks has exactly fifteen
blocks and is isomorphic to an entry in the explicit 68-entry catalogue. -/
theorem gppt_classification {C : Family (Fin 12)}
    (hC : IsCover C 6 3) (hb : C.card ≤ 15) :
    C.card = 15 ∧ ∃ i : Fin 68, Isomorphic C (linkRepresentative i) := by
  have hc : C.card = 15 :=
    le_antisymm hb (GPPTStructural.lower_bound_fifteen (by simp) hC)
  refine ⟨hc, ?_⟩
  rcases gppt_structural_reduction hC hc with ht | he
  · exact ht.classification
  · exact ⟨67, GPPTStructural.figure6_eq_exceptional ▸ he⟩

theorem lower_bound_12_6_3 {α : Type*} [Fintype α] [DecidableEq α]
    (hn : Fintype.card α = 12) {C : Family α} (hC : IsCover C 6 3) :
    15 ≤ C.card := GPPTStructural.lower_bound_fifteen hn hC

theorem gppt_classification_on {α : Type*} [Fintype α] [DecidableEq α]
    (hn : Fintype.card α = 12) {C : Family α}
    (hC : IsCover C 6 3) (hb : C.card ≤ 15) :
    C.card = 15 ∧ ∃ i : Fin 68, Isomorphic C (linkRepresentative i) := by
  let e : α ≃ Fin 12 := Fintype.equivFinOfCardEq hn
  obtain ⟨hc, i, hi⟩ := gppt_classification (relabel_isCover e hC)
    (by simpa only [relabel_card] using hb)
  exact ⟨by simpa only [relabel_card] using hc, i, Isomorphic.trans ⟨e, rfl⟩ hi⟩

/-- The equality C(12,6,3)=15, expressed by a witness and a universal bound. -/
theorem covering_number_12_6_3 :
    (∃ C : Family (Fin 12), IsCover C 6 3 ∧ C.card = 15) ∧
    (∀ C : Family (Fin 12), IsCover C 6 3 → 15 ≤ C.card) :=
  ⟨⟨figure6, figure6_isCover, figure6_card⟩,
    fun _ hC => lower_bound_12_6_3 (by simp) hC⟩

#print axioms gppt_classification
#print axioms covering_number_12_6_3

#guard_standard_axioms gppt_structural_reduction gppt_classification
  gppt_classification_on lower_bound_12_6_3 covering_number_12_6_3

end CoveringDesigns
