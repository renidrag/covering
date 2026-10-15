import CoveringDesigns.C12_6_3.Witnesses
import CoveringDesigns.Foundations.StarRelabelling
import Mathlib.Data.Fin.VecNotation

/-!
The partial covering in GPPT Figure 1 and its normalized form in Figure 4.

The fixed permutation below is the one printed in the proof of Lemma 5.7:
`(267T8)(13954)`, with `T = 10` and `E = 11`.  The Figure 4 data were
also checked against the retained paper's table on page 11.  This module
checks only these fixed data; it makes no claim that arbitrary minimum
coverings have this form.  That structural reduction is a separate theorem.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace CoveringDesigns.GPPTStructural

open Finset

/-- The twelve complete blocks in GPPT Figure 1. -/
def core : Family (Fin 12) := figure1.filter (fun B => B.card = 6)

/-- The three four-point blocks that remain to be completed. -/
def spine : Fin 3 → Finset (Fin 12) :=
  ![{0, 1, 2, 3}, {4, 5, 6, 7}, {8, 9, 10, 11}]

/-- Choose two further points for each of the three incomplete blocks. -/
def ValidAdditions (R : Fin 3 → Finset (Fin 12)) : Prop :=
  ∀ i, R i ⊆ univ \ spine i ∧ (R i).card = 2

def templateBlocks (R : Fin 3 → Finset (Fin 12)) : Family (Fin 12) :=
  core ∪ univ.image (fun i => spine i ∪ R i)

def IsTemplateCompletion (C : Family (Fin 12)) : Prop :=
  ∃ R, ValidAdditions R ∧ C = templateBlocks R

def IsomorphicTemplateCompletion (C : Family (Fin 12)) : Prop :=
  ∃ D, IsTemplateCompletion D ∧ Isomorphic C D

theorem core_card : core.card = 12 := by decide +kernel

theorem core_uniform : Uniform core 6 := by
  intro B hB
  exact (mem_filter.mp hB).2

theorem spine_card : ∀ i, (spine i).card = 4 := by decide +kernel

theorem spine_eq_quarter :
    ∀ i, spine i = univ.filter (fun x => x.val / 4 = i.val) := by
  decide +kernel

theorem spine_eq_filter (i : Fin 3) :
    spine i = univ.filter (fun x : Fin 12 => x.val / 4 = i.val) :=
  spine_eq_quarter i

theorem figure1_eq_core_spines :
    figure1 = core ∪ univ.image spine := by decide +kernel

/-- An equivalent form that specifies the three completed six-point blocks. -/
theorem isTemplateCompletion_iff_extensions (C : Family (Fin 12)) :
    IsTemplateCompletion C ↔
      ∃ B : Fin 3 → Finset (Fin 12),
        (∀ i, spine i ⊆ B i ∧ (B i).card = 6) ∧
        C = core ∪ univ.image B := by
  constructor
  · rintro ⟨R, hR, rfl⟩
    refine ⟨fun i => spine i ∪ R i, ?_, rfl⟩
    intro i
    refine ⟨subset_union_left, ?_⟩
    have hd : Disjoint (spine i) (R i) := by
      apply disjoint_left.mpr
      intro x hx hxR
      exact (mem_sdiff.mp ((hR i).1 hxR)).2 hx
    rw [card_union_of_disjoint hd, spine_card, (hR i).2]
  · rintro ⟨B, hB, rfl⟩
    refine ⟨fun i => B i \ spine i, ?_, ?_⟩
    · intro i
      constructor
      · intro x hx
        exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
      · rw [card_sdiff_of_subset (hB i).1, (hB i).2, spine_card]
    · unfold templateBlocks
      congr 1
      apply congrArg (univ.image)
      funext i
      exact (union_sdiff_of_subset (hB i).1).symm

/-- The twelve six-point blocks printed in GPPT Figure 4. -/
def figure4Core : Family (Fin 12) := {
  {0, 1, 2, 3, 4, 5},
  {0, 1, 2, 6, 7, 8},
  {0, 1, 2, 9, 10, 11},
  {0, 3, 7, 8, 10, 11},
  {0, 4, 5, 6, 10, 11},
  {0, 4, 5, 7, 8, 9},
  {1, 4, 6, 8, 9, 11},
  {1, 3, 5, 7, 9, 11},
  {1, 3, 5, 6, 8, 10},
  {2, 5, 6, 7, 9, 10},
  {2, 3, 4, 8, 9, 10},
  {2, 3, 4, 6, 7, 11}}

def figure4Spine : Fin 3 → Finset (Fin 12) :=
  ![{0, 3, 6, 9}, {1, 4, 7, 10}, {2, 5, 8, 11}]

def figure4 : Family (Fin 12) := figure4Core ∪ univ.image figure4Spine

def ValidFigure4Additions (R : Fin 3 → Finset (Fin 12)) : Prop :=
  ∀ i, R i ⊆ univ \ figure4Spine i ∧ (R i).card = 2

def figure4TemplateBlocks (R : Fin 3 → Finset (Fin 12)) : Family (Fin 12) :=
  figure4Core ∪ univ.image (fun i => figure4Spine i ∪ R i)

def IsFigure4Completion (C : Family (Fin 12)) : Prop :=
  ∃ R, ValidFigure4Additions R ∧ C = figure4TemplateBlocks R

theorem figure4Spine_card : ∀ i, (figure4Spine i).card = 4 := by decide +kernel

theorem isFigure4Completion_iff_extensions (C : Family (Fin 12)) :
    IsFigure4Completion C ↔
      ∃ B : Fin 3 → Finset (Fin 12),
        (∀ i, figure4Spine i ⊆ B i ∧ (B i).card = 6) ∧
        C = figure4Core ∪ univ.image B := by
  constructor
  · rintro ⟨R, hR, rfl⟩
    refine ⟨fun i => figure4Spine i ∪ R i, ?_, rfl⟩
    intro i
    refine ⟨subset_union_left, ?_⟩
    have hd : Disjoint (figure4Spine i) (R i) := by
      apply disjoint_left.mpr
      intro x hx hxR
      exact (mem_sdiff.mp ((hR i).1 hxR)).2 hx
    rw [card_union_of_disjoint hd, figure4Spine_card, (hR i).2]
  · rintro ⟨B, hB, rfl⟩
    refine ⟨fun i => B i \ figure4Spine i, ?_, ?_⟩
    · intro i
      constructor
      · intro x hx
        exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
      · rw [card_sdiff_of_subset (hB i).1, (hB i).2, figure4Spine_card]
    · unfold figure4TemplateBlocks
      congr 1
      apply congrArg (univ.image)
      funext i
      exact (union_sdiff_of_subset (hB i).1).symm

/-- The paper's point permutation from Figure 1 to Figure 4. -/
def figure1To4 : Equiv.Perm (Fin 12) where
  toFun := ![0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8, 11]
  invFun := ![0, 4, 8, 1, 5, 9, 2, 6, 10, 3, 7, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem relabel_core : relabel figure1To4 core = figure4Core := by
  decide +kernel

theorem map_spine :
    ∀ i, (spine i).map figure1To4.toEmbedding = figure4Spine i := by
  decide +kernel

theorem relabel_figure1 : relabel figure1To4 figure1 = figure4 := by
  decide +kernel

theorem figure1_isomorphic_figure4 : Isomorphic figure1 figure4 :=
  ⟨figure1To4, relabel_figure1⟩

theorem figure4_isomorphic_figure1 : Isomorphic figure4 figure1 := by
  refine ⟨figure1To4.symm, ?_⟩
  rw [← relabel_figure1, relabel_symm_relabel]

/-- Relabelling commutes with filling a fixed finite list of incomplete blocks. -/
theorem relabel_completion_blocks (e : Equiv.Perm (Fin 12))
    (K : Family (Fin 12)) (P R : Fin 3 → Finset (Fin 12)) :
    relabel e (K ∪ univ.image (fun i => P i ∪ R i)) =
      relabel e K ∪
        univ.image (fun i => (P i).map e.toEmbedding ∪ (R i).map e.toEmbedding) := by
  ext B
  constructor
  · intro h
    obtain ⟨A, hA, rfl⟩ := mem_map.mp h
    rcases mem_union.mp hA with hK | hR
    · exact mem_union_left _ ((mem_relabel e K A).mpr hK)
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hR
      exact mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, (map_union _ _).symm⟩)
  · intro h
    rcases mem_union.mp h with hK | hR
    · obtain ⟨A, hA, rfl⟩ := mem_map.mp hK
      exact mem_map.mpr ⟨A, mem_union_left _ hA, rfl⟩
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hR
      exact mem_map.mpr ⟨P i ∪ R i,
        mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩), map_union _ _⟩

theorem relabel_templateBlocks (R : Fin 3 → Finset (Fin 12)) :
    relabel figure1To4 (templateBlocks R) =
      figure4TemplateBlocks (fun i => (R i).map figure1To4.toEmbedding) := by
  unfold templateBlocks figure4TemplateBlocks
  rw [relabel_completion_blocks, relabel_core]
  simp only [map_spine]

private theorem additions_map (e : Equiv.Perm (Fin 12))
    (P R : Fin 3 → Finset (Fin 12))
    (hR : ∀ i, R i ⊆ univ \ P i ∧ (R i).card = 2) :
    ∀ i, (R i).map e.toEmbedding ⊆ univ \ (P i).map e.toEmbedding ∧
      ((R i).map e.toEmbedding).card = 2 := by
  intro i
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    simp only [mem_sdiff, mem_univ, true_and, mem_map_equiv]
    simpa using (mem_sdiff.mp ((hR i).1 hy)).2
  · simpa using (hR i).2

theorem validAdditions_map {R : Fin 3 → Finset (Fin 12)}
    (hR : ValidAdditions R) :
    ValidFigure4Additions (fun i => (R i).map figure1To4.toEmbedding) := by
  simpa only [ValidFigure4Additions, map_spine] using
    additions_map figure1To4 spine R hR

theorem figure4Completion_of_templateCompletion {C : Family (Fin 12)}
    (hC : IsTemplateCompletion C) : IsFigure4Completion (relabel figure1To4 C) := by
  obtain ⟨R, hR, rfl⟩ := hC
  exact ⟨_, validAdditions_map hR, relabel_templateBlocks R⟩

theorem figure4Completion_isomorphicTemplateCompletion {C : Family (Fin 12)}
    (hC : IsFigure4Completion C) : IsomorphicTemplateCompletion C := by
  obtain ⟨R, hR, rfl⟩ := hC
  let R' : Fin 3 → Finset (Fin 12) := fun i => (R i).map figure1To4.symm.toEmbedding
  have hsp (i : Fin 3) :
      (figure4Spine i).map figure1To4.symm.toEmbedding = spine i := by
    rw [← map_spine i]
    ext x
    simp only [mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hR' : ValidAdditions R' := by
    simpa only [ValidAdditions, R', hsp] using
      additions_map figure1To4.symm figure4Spine R hR
  refine ⟨templateBlocks R', ⟨R', hR', rfl⟩, figure1To4.symm, ?_⟩
  have hc : relabel figure1To4.symm figure4Core = core := by
    rw [← relabel_core, relabel_symm_relabel]
  unfold figure4TemplateBlocks templateBlocks
  rw [relabel_completion_blocks, hc]
  simp only [hsp, R']

#print axioms figure4Completion_isomorphicTemplateCompletion

end CoveringDesigns.GPPTStructural
