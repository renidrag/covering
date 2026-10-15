import CoveringDesigns.C12_6_3.Structural.Triplicate

/-!
Changing the order of the roots and triads does not change a triplicate frame's
covering. The finite index helpers name any three distinct indices in a chosen
order; they impose no symmetry assumption on the covering.
-/

namespace CoveringDesigns.GPPTStructural

open Finset

/-- The permutation sending `0, 1, 2` to any three distinct indices. -/
noncomputable def fin3_indexPerm (r s t : Fin 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) : Equiv.Perm (Fin 3) := by
  let f : Fin 3 → Fin 3 := ![r, s, t]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  exact Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩

@[simp] theorem fin3_indexPerm_zero (r s t : Fin 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    fin3_indexPerm r s t hrs hrt hst 0 = r := rfl

@[simp] theorem fin3_indexPerm_one (r s t : Fin 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    fin3_indexPerm r s t hrs hrt hst 1 = s := rfl

@[simp] theorem fin3_indexPerm_two (r s t : Fin 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    fin3_indexPerm r s t hrs hrt hst 2 = t := rfl

/-- Two distinct indices leave a third index. -/
theorem fin3_exists_third {r s : Fin 3} (hrs : r ≠ s) :
    ∃ t : Fin 3, r ≠ t ∧ s ≠ t := by
  fin_cases r <;> fin_cases s <;> simp_all <;> decide

namespace TriplicateFrame

variable {α : Type*} [DecidableEq α] [Fintype α]
  {C : Family α} (F : TriplicateFrame C)

/-- Reorder the three roots and the three triads independently. -/
def reindex (ρ σ : Equiv.Perm (Fin 3)) : TriplicateFrame C where
  roots r := F.roots (ρ r)
  roots_injective := F.roots_injective.comp ρ.injective
  common := {
    triad j := F.common.triad (σ j)
    triad_card j := F.common.triad_card (σ j)
    pairwise_disjoint _ _ hij := F.common.pairwise_disjoint (fun he => hij (σ.injective he))
    disjoint_root j := by simpa only [univ_image_perm] using F.common.disjoint_root (σ j)
    spans := by rw [univ_image_perm, univ_biUnion_perm, F.common.spans] }
  row r := {
    selected j := (F.row (ρ r)).selected (σ j)
    selected_mem j := (F.row (ρ r)).selected_mem (σ j)
    shortTrace := (F.row (ρ r)).shortTrace
    shortTrace_card := (F.row (ρ r)).shortTrace_card
    root_not_mem_shortTrace := (F.row (ρ r)).root_not_mem_shortTrace
    selected_subset := by simpa only [univ_image_perm] using (F.row (ρ r)).selected_subset
    selected_iff := by simpa only [univ_image_perm] using (F.row (ρ r)).selected_iff
    short_iff := (F.row (ρ r)).short_iff
    star_eq := by
      simp only [univ_image_perm, markedRow_reindex]
      rw [univ_image_perm σ (fun j => univ.image F.roots ∪ F.common.triad j),
        univ_image_perm σ (fun j => insert (F.roots (ρ r))
          (StantonGeometry.markedRow F.common.triad (F.row (ρ r)).selected j))]
      exact (F.row (ρ r)).star_eq }
  root_degree r := F.root_degree (ρ r)
  short_disjoint_roots r := by
    simpa only [univ_image_perm] using F.short_disjoint_roots (ρ r)
  blocks_eq := by
    simp only [univ_image_perm, markedRow_reindex]
    rw [univ_image_perm σ (fun j => univ.image F.roots ∪ F.common.triad j)]
    have hrows (r : Fin 3) :
        univ.image (fun j => insert (F.roots (ρ r))
          (StantonGeometry.markedRow F.common.triad (F.row (ρ r)).selected (σ j))) =
        univ.image (fun j => insert (F.roots (ρ r))
          (StantonGeometry.markedRow F.common.triad (F.row (ρ r)).selected j)) :=
      univ_image_perm σ (fun j => insert (F.roots (ρ r))
        (StantonGeometry.markedRow F.common.triad (F.row (ρ r)).selected j))
    simp_rw [hrows]
    rw [univ_biUnion_perm ρ (fun r => univ.image (fun j => insert (F.roots r)
      (StantonGeometry.markedRow F.common.triad (F.row r).selected j))),
      univ_image_perm ρ (fun r => insert (F.roots r) (F.row r).shortTrace)]
    exact F.blocks_eq

@[simp] theorem reindex_roots (ρ σ : Equiv.Perm (Fin 3)) (r : Fin 3) :
    (F.reindex ρ σ).roots r = F.roots (ρ r) := rfl

@[simp] theorem reindex_triad (ρ σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (F.reindex ρ σ).common.triad j = F.common.triad (σ j) := rfl

@[simp] theorem reindex_selected (ρ σ : Equiv.Perm (Fin 3)) (r j : Fin 3) :
    ((F.reindex ρ σ).row r).selected j = (F.row (ρ r)).selected (σ j) := rfl

@[simp] theorem reindex_shortTrace (ρ σ : Equiv.Perm (Fin 3)) (r : Fin 3) :
    ((F.reindex ρ σ).row r).shortTrace = (F.row (ρ r)).shortTrace := rfl

end TriplicateFrame

#guard_standard_axioms fin3_indexPerm fin3_exists_third TriplicateFrame.reindex

end CoveringDesigns.GPPTStructural
