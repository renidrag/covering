import CoveringDesigns.C19_9_3.ShortCompletion
import CoveringDesigns.Foundations.IndexedPadding

/-! Unconditional lower seventeen. All actual-link and affine hypotheses
are derived internally; padding retains repeated occurrence images. -/
namespace CoveringDesigns.C19_9_3
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

/-- Sixteen actual indexed occurrences are impossible. -/
theorem no_sixteen {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16) : False := by
  classical
  obtain ⟨C⟩ := actual_weak_completion hv h hi
  apply weak_completion_impossible C
  rw [Fintype.card_subtype_compl,Fintype.card_coe,hv,minimum_points_card hv h hi]

/-- Every indexed triple covering by nine-sets on nineteen points has at
least seventeen occurrences, with no distinctness or structural premise. -/
theorem seventeen_le_card {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) : 17 ≤ Fintype.card I := by
  apply IndexedPadding.lower_of_fixed_exclusion (b := 16) (by omega : 3 ≤ Fintype.card V) h
  intro D hD
  exact no_sixteen hv hD (Fintype.card_fin 16)

/-- Expanded indexed covering condition, including arbitrary point and
occurrence types. No auxiliary incidence or geometry assumptions occur. -/
theorem seventeen_le_card_expanded (B : I → Finset V) (hv : Fintype.card V = 19)
    (hu : ∀ i, (B i).card = 9)
    (hc : ∀ T : Finset V, T.card = 3 → ∃ i, T ⊆ B i) : 17 ≤ Fintype.card I :=
  seventeen_le_card hv ⟨hu,(Multicover.covers_one_iff B 3).mpr hc⟩

#guard_standard_axioms no_sixteen seventeen_le_card seventeen_le_card_expanded
end CoveringDesigns.C19_9_3

namespace CoveringDesigns
open Finset

theorem lower_bound_19_9_3_on {V : Type*} [Fintype V] [DecidableEq V]
    (hv : Fintype.card V = 19) {C : Family V} (h : IsCover C 9 3) : 17 ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using
    C19_9_3.seventeen_le_card hv ((Multicover.ofFamily_isCover_one C 9 3).mpr h)

theorem lower_bound_19_9_3 {C : Family (Fin 19)} (h : IsCover C 9 3) : 17 ≤ C.card :=
  lower_bound_19_9_3_on (by simp) h

theorem lower_bound_19_9_3_expanded {V : Type*} [Fintype V] [DecidableEq V]
    (hv : Fintype.card V = 19) (C : Finset (Finset V))
    (hu : ∀ B ∈ C, B.card = 9)
    (hc : ∀ T : Finset V, T.card = 3 → ∃ B ∈ C, T ⊆ B) : 17 ≤ C.card :=
  lower_bound_19_9_3_on hv ⟨hu,hc⟩

#guard_standard_axioms lower_bound_19_9_3_on lower_bound_19_9_3 lower_bound_19_9_3_expanded
end CoveringDesigns
