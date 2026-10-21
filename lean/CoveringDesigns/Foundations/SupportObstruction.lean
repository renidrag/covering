import CoveringDesigns.Foundations.Basic
import Mathlib.Data.Finset.Card

/-! Inclusion–exclusion on actual finite occurrence indices. Repeated block
values and equal point supports are allowed. Actual point labels stay distinct. -/
namespace CoveringDesigns.SupportObstruction
open Finset
variable {ι α : Type*} [DecidableEq ι]

/-- A subtraction-free form valid without truncated natural subtraction. -/
theorem intersection_identity (I A H S T : Finset ι)
    (hH : H ⊆ I) (hunion : S ∪ T = I \ A) :
    ((H ∩ S) ∩ T).card + H.card =
      (H ∩ S).card + (H ∩ T).card + (H ∩ A).card := by
  have hi := card_union_add_card_inter (H ∩ S) (H ∩ T)
  have hu : (H ∩ S) ∪ (H ∩ T) = H \ A := by
    rw [← inter_union_distrib_left, hunion]
    ext i
    simp only [mem_inter, mem_sdiff]
    exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,hH h.1,h.2⟩⟩
  have he : (H ∩ S) ∩ (H ∩ T) = (H ∩ S) ∩ T := by
    ext i
    simp only [mem_inter]
    tauto
  rw [hu,he] at hi
  have hd := card_sdiff_add_card_inter H A
  omega

/-- The bound is stated additively, so all zero/empty boundary cases are safe. -/
theorem empty_of_intersection_bound (I A H S T : Finset ι)
    (hH : H ⊆ I) (hunion : S ∪ T = I \ A)
    (hbound : (H ∩ S).card + (H ∩ T).card + (H ∩ A).card ≤ H.card) :
    (H ∩ S) ∩ T = ∅ := by
  have hi := intersection_identity I A H S T hH hunion
  apply card_eq_zero.mp
  omega

/-- A triple-covering contradiction retains three distinct actual point labels.
The block map need not be injective. -/
theorem uncovered_triple [Fintype ι] [DecidableEq α]
    (B : ι → Finset α) (h x y : α) (hhx : h ≠ x) (hhy : h ≠ y) (hxy : x ≠ y)
    (hempty : ((univ.filter (fun i => h ∈ B i)) ∩
      (univ.filter (fun i => x ∈ B i))) ∩
      (univ.filter (fun i => y ∈ B i)) = ∅)
    (hcover : ∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) : False := by
  obtain ⟨i, hi⟩ := hcover {h,x,y} (by simp [hhx,hhy,hxy])
  have hm : i ∈ ((univ.filter (fun i => h ∈ B i)) ∩
      (univ.filter (fun i => x ∈ B i))) ∩
      (univ.filter (fun i => y ∈ B i)) := by
    simp only [mem_inter, mem_filter, mem_univ, true_and]
    exact ⟨⟨hi (by simp),hi (by simp)⟩,hi (by simp)⟩
  rw [hempty] at hm
  exact notMem_empty i hm

end CoveringDesigns.SupportObstruction
