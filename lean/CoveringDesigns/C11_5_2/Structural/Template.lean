import CoveringDesigns.C11_5_2.Representatives
import CoveringDesigns.Foundations.StarRelabelling
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Fin.VecNotation

/-! The final, structural part of the Stanton classification.

The labels are a=0, s=1, t=2 and the four pairs
F={3,4}, G={5,6}, C={7,8}, D={9,10}.  A completion adds an arbitrary pair
R from C union D to the final triple.  Within-pair permutations, and the
simultaneous swaps C/D and s/t, reduce every R to a whole pair or a transversal.

Only the displayed fixed witnesses and displayed point permutations are
checked by kernel evaluation.  There is no enumeration of covering families,
classification assumption, SAT proof, or native evaluation in this file. -/

namespace CoveringDesigns.StantonStructural

open Finset

def spine : Finset (Fin 11) := {0, 1, 2}
def pairC : Finset (Fin 11) := {7, 8}
def pairD : Finset (Fin 11) := {9, 10}

def coreSix : Family (Fin 11) :=
  {{0, 3, 4, 5, 6},
   {1, 3, 4, 7, 8}, {2, 3, 4, 9, 10},
   {1, 5, 6, 9, 10}, {2, 5, 6, 7, 8},
   {0, 7, 8, 9, 10}}

def templateBlocks (R : Finset (Fin 11)) : Family (Fin 11) :=
  insert (spine ∪ R) coreSix

section FixedWitnesses
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

private theorem coreSix_uniform : Uniform coreSix 5 := by
  unfold Uniform
  decide +kernel

private theorem coreSix_card : coreSix.card = 6 := by decide +kernel

private theorem coreSix_missing_spine : ∀ B ∈ coreSix, ¬ spine ⊆ B := by
  decide +kernel

private theorem spine_disjoint_pairs : Disjoint spine (pairC ∪ pairD) := by
  decide +kernel

private theorem core_with_triple_covers : Covers (insert spine coreSix) 2 := by
  apply covers_of_powersetCard
  decide +kernel

end FixedWitnesses

theorem templateBlocks_uniform {R : Finset (Fin 11)}
    (hR : R ⊆ pairC ∪ pairD) (hr : R.card = 2) : Uniform (templateBlocks R) 5 := by
  intro B hB
  obtain rfl | hB := mem_insert.mp hB
  · rw [card_union_of_disjoint (spine_disjoint_pairs.mono_right hR), hr]
    have hs : spine.card = 3 := by decide +kernel
    rw [hs]
  · exact coreSix_uniform B hB

theorem templateBlocks_card (R : Finset (Fin 11)) : (templateBlocks R).card = 7 := by
  have hn : spine ∪ R ∉ coreSix := by
    intro h
    exact coreSix_missing_spine _ h subset_union_left
  rw [templateBlocks, card_insert_of_notMem hn, coreSix_card]

theorem templateBlocks_covers (R : Finset (Fin 11)) : Covers (templateBlocks R) 2 := by
  intro T ht
  obtain ⟨B, hB, hT⟩ := core_with_triple_covers T ht
  obtain rfl | hB := mem_insert.mp hB
  · exact ⟨spine ∪ R, mem_insert_self _ _, hT.trans subset_union_left⟩
  · exact ⟨B, mem_insert_of_mem hB, hT⟩

theorem templateBlocks_isCover {R : Finset (Fin 11)}
    (hR : R ⊆ pairC ∪ pairD) (hr : R.card = 2) : IsCover (templateBlocks R) 5 2 :=
  ⟨templateBlocks_uniform hR hr, templateBlocks_covers R⟩

/-- A pair in the union of two pairs is either a whole pair or a transversal.
This is a set-theoretic dichotomy, not a finite configuration search. -/
theorem pair_completion_cases {α : Type*} [DecidableEq α]
    {C D R : Finset α} (hc : C.card = 2) (hd : D.card = 2)
    (hr : R.card = 2) (hR : R ⊆ C ∪ D) :
    R = C ∨ R = D ∨ ∃ c ∈ C, ∃ d ∈ D, R = {c, d} := by
  classical
  by_cases hRC : R ⊆ C
  · exact Or.inl (eq_of_subset_of_card_le hRC (by omega))
  by_cases hRD : R ⊆ D
  · exact Or.inr (Or.inl (eq_of_subset_of_card_le hRD (by omega)))
  obtain ⟨c, hcR, hcD⟩ := not_subset.mp hRD
  obtain ⟨d, hdR, hdC⟩ := not_subset.mp hRC
  have hcC : c ∈ C := (mem_union.mp (hR hcR)).resolve_right hcD
  have hdD : d ∈ D := (mem_union.mp (hR hdR)).resolve_left hdC
  have hcd : c ≠ d := fun he => hdC (he ▸ hcC)
  refine Or.inr (Or.inr ⟨c, hcC, d, hdD, ?_⟩)
  symm
  apply eq_of_subset_of_card_le
  · simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hcR, hdR⟩
  · simp [hcd, hr]

def swapSides : Equiv.Perm (Fin 11) where
  toFun := ![0, 2, 1, 3, 4, 5, 6, 9, 10, 7, 8]
  invFun := ![0, 2, 1, 3, 4, 5, 6, 9, 10, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def wholePairToRepresentative : Equiv.Perm (Fin 11) where
  toFun := ![8, 9, 10, 2, 6, 3, 7, 0, 4, 1, 5]
  invFun := ![7, 9, 3, 5, 8, 10, 4, 6, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def transversalToRepresentative : Equiv.Perm (Fin 11) where
  toFun := ![2, 0, 1, 5, 7, 6, 8, 3, 9, 4, 10]
  invFun := ![1, 2, 0, 7, 9, 3, 5, 4, 6, 8, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem whole_pair_to_representative :
    relabel wholePairToRepresentative (templateBlocks pairC) = stantonRepresentative true := by
  decide +kernel

theorem transversal_to_representative :
    relabel transversalToRepresentative (templateBlocks {7, 9}) = stantonRepresentative false := by
  decide +kernel

private theorem other_pair_isomorphic : Isomorphic (templateBlocks pairD) (templateBlocks pairC) := by
  exact ⟨swapSides, by decide +kernel⟩

private theorem transversal_isomorphic {c d : Fin 11}
    (hc : c ∈ pairC) (hd : d ∈ pairD) :
    Isomorphic (templateBlocks {c, d}) (templateBlocks {7, 9}) := by
  simp only [pairC, pairD, mem_insert, mem_singleton] at hc hd
  obtain rfl | rfl := hc <;> obtain rfl | rfl := hd
  · exact ⟨Equiv.refl _, relabel_refl _⟩
  · exact ⟨Equiv.swap 9 10, by decide +kernel⟩
  · exact ⟨Equiv.swap 7 8, by decide +kernel⟩
  · exact ⟨(Equiv.swap 7 8).trans (Equiv.swap 9 10), by decide +kernel⟩

/-- Every completion of the structural template is isomorphic to one of the
two explicit representatives. -/
theorem template_classification {R : Finset (Fin 11)}
    (hR : R ⊆ pairC ∪ pairD) (hr : R.card = 2) :
    ∃ tag, Isomorphic (templateBlocks R) (stantonRepresentative tag) := by
  obtain h | h | ⟨c, hc, d, hd, h⟩ := pair_completion_cases
    (C := pairC) (D := pairD) (by decide +kernel) (by decide +kernel) hr hR
  · subst R
    exact ⟨true, wholePairToRepresentative, whole_pair_to_representative⟩
  · subst R
    exact ⟨true, other_pair_isomorphic.trans
      ⟨wholePairToRepresentative, whole_pair_to_representative⟩⟩
  · subst R
    exact ⟨false, (transversal_isomorphic hc hd).trans
      ⟨transversalToRepresentative, transversal_to_representative⟩⟩

/-- The abstract template after choosing labels for the four disjoint pairs.
The graph-to-template argument supplies this record; this module proves all
claims about its completions. -/
structure StantonTemplate {α : Type*} [DecidableEq α] (C : Family α) where
  label : Fin 11 ≃ α
  additions : Finset (Fin 11)
  additions_subset : additions ⊆ pairC ∪ pairD
  additions_card : additions.card = 2
  blocks_eq : relabel label (templateBlocks additions) = C

theorem StantonTemplate.isCover {α : Type*} [DecidableEq α] {C : Family α}
    (h : StantonTemplate C) : IsCover C 5 2 := by
  rw [← h.blocks_eq]
  exact relabel_isCover h.label (templateBlocks_isCover h.additions_subset h.additions_card)

theorem StantonTemplate.card {α : Type*} [DecidableEq α] {C : Family α}
    (h : StantonTemplate C) : C.card = 7 := by
  rw [← h.blocks_eq, relabel_card, templateBlocks_card]

theorem StantonTemplate.classification {α : Type*} [DecidableEq α] {C : Family α}
    (h : StantonTemplate C) : ∃ tag, Isomorphic C (stantonRepresentative tag) := by
  obtain ⟨tag, ht⟩ := template_classification h.additions_subset h.additions_card
  refine ⟨tag, Isomorphic.trans ?_ ht⟩
  refine ⟨h.label.symm, ?_⟩
  have he := congrArg (relabel h.label.symm) h.blocks_eq
  simpa only [relabel_symm_relabel] using he.symm

#guard_standard_axioms templateBlocks_isCover templateBlocks_card template_classification
  StantonTemplate.isCover StantonTemplate.card StantonTemplate.classification

end CoveringDesigns.StantonStructural
