import CoveringDesigns.C11_5_2.Geometry.Basic

namespace CoveringDesigns.StantonGeometry

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {C : Family α} {K : Finset α} (F : MarkingFrame C K)

theorem MarkingFrame.shortBlock_isShort : IsShortBlock C F.shortBlock :=
  (F.short_iff _).mpr rfl

theorem MarkingFrame.shortBlock_mem : F.shortBlock ∈ C := F.shortBlock_isShort.1

theorem MarkingFrame.selected_short (i : Fin 3) : IsShortPoint C (F.selected i) :=
  (F.selected_iff _).mp (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

theorem MarkingFrame.selected_in_short (i : Fin 3) : F.selected i ∈ F.shortBlock :=
  F.selected_subset (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

theorem MarkingFrame.short_meets_triad (i : Fin 3) : (F.shortBlock ∩ F.triads i).Nonempty :=
  ⟨F.selected i, mem_inter.mpr ⟨F.selected_in_short i, F.selected_mem i⟩⟩

theorem MarkingFrame.row_meets_triad (i j : Fin 3) :
    (markedRow F.triads F.selected i ∩ F.triads j).Nonempty := by
  by_cases hji : j = i
  · subst j
    refine ⟨F.selected i, mem_inter.mpr ⟨?_, F.selected_mem i⟩⟩
    exact mem_union_left _ (mem_singleton_self _)
  · have hc : (F.triads j \ {F.selected j}).card = 2 := by
      rw [card_sdiff_of_subset (singleton_subset_iff.mpr (F.selected_mem j)), F.triad_card]
      simp
    obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (F.triads j \ {F.selected j}).card by omega)
    refine ⟨x, mem_inter.mpr ⟨?_, (mem_sdiff.mp hx).1⟩⟩
    exact mem_union_right _ (mem_biUnion.mpr ⟨j, mem_erase.mpr ⟨hji, mem_univ _⟩, hx⟩)

/-- Every unmarked full row, and the short block, meets each marked triad. -/
theorem MarkingFrame.nonmarked_meets_triad {B : Finset α}
    (hB : B ∈ C) (hK : ¬ K ⊆ B) (i : Fin 3) : (B ∩ F.triads i).Nonempty := by
  rw [F.blocks_eq] at hB
  rcases mem_insert.mp hB with rfl | hB
  · exact F.short_meets_triad i
  rcases mem_union.mp hB with hB | hB
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hB
    exact False.elim (hK subset_union_left)
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hB
    exact F.row_meets_triad j i

#guard_standard_axioms MarkingFrame.nonmarked_meets_triad

end CoveringDesigns.StantonGeometry
