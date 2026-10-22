import CoveringDesigns.C14_5_3

/-! Boundary checks for occurrence deletion and irredundancy. -/
namespace CoveringDesigns.C14_5_3.Boundary
open Finset

/-- Two equal occurrences still cover triples. Coverage alone does not imply
irredundancy or occurrence injectivity. -/
def repeated : Fin 2 → Finset (Fin 5) := fun _ => univ

theorem repeated_cover : Multicover.IsCover repeated 5 3 1 := by
  refine ⟨fun _ => by simp [repeated],(Multicover.covers_one_iff _ _).mpr ?_⟩
  intro T ht
  exact ⟨0,subset_univ T⟩

theorem repeated_not_irredundant : ¬ Irredundant repeated 3 := by
  intro h
  have hi := h.injective (show repeated 0 = repeated 1 from rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) hi

theorem delete_one_still_covers :
    Multicover.IsCover (fun i : {i : Fin 2 // i ≠ 0} => repeated i.val) 5 3 1 := by
  refine ⟨fun _ => by simp [repeated],(Multicover.covers_one_iff _ _).mpr ?_⟩
  intro T ht
  exact ⟨⟨1,by decide⟩,subset_univ T⟩

theorem delete_all_copies_fails :
    ¬ Multicover.IsCover (fun i : {i : Fin 2 // repeated i ≠ repeated 0} => repeated i.val) 5 3 1 := by
  intro h
  obtain ⟨i,hi⟩ := (Multicover.covers_one_iff _ _).mp h.2 {0,1,2} (by decide)
  exact i.property rfl

theorem deletion_counts_one_occurrence :
    Fintype.card {i : Fin 2 // i ≠ 0} = 1 ∧
      Fintype.card {i : Fin 2 // repeated i ≠ repeated 0} = 0 := by decide +kernel

/-- The almost-exact interface does not assume distinct block values. -/
theorem almost_exact_without_injectivity {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] (B : ι → Finset α)
    (hv : Fintype.card α = 13) (hn : Fintype.card ι = 14)
    (hu : ∀ i, (B i).card = 4)
    (hc : ∀ P : Finset α, P.card = 2 → ∃ i, P ⊆ B i) :
    ∃ i, B i = linkHighPoints B ∧
      ExactDesign.IsDesign (fun j : {j // j ≠ i} => B j.val) 4 2 1 :=
  almost_exact_deletion hv ⟨hu,(Multicover.covers_one_iff B 2).mpr hc⟩ hn

/-- Forty-cover irredundancy is derived from the earlier unconditional bound. -/
theorem forty_private_without_structural_premises {α ι : Type*} [Fintype α]
    [DecidableEq α] [Fintype ι] (B : ι → Finset α)
    (hv : Fintype.card α = 14) (hn : Fintype.card ι = 40)
    (hu : ∀ i, (B i).card = 5)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) :
    ∀ i, ∃ T : Finset α, T.card = 3 ∧ T ⊆ B i ∧ ∀ j, T ⊆ B j → j = i :=
  forty_irredundant hv ⟨hu,(Multicover.covers_one_iff B 3).mpr hc⟩ hn

end CoveringDesigns.C14_5_3.Boundary
