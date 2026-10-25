import CoveringDesigns.ProjectiveLinkBounds.Weak
import CoveringDesigns.ProjectiveLinkBounds.Deletion

/-! Unconditional indexed and ordinary family bounds. No geometric existence,
minimum degree, selected link or injectivity hypothesis remains. -/
namespace CoveringDesigns.ProjectiveLinkBounds
open Finset Internal
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem indexed_lower_bound {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {B : ι → Finset α} (hv : Fintype.card α = q^2+q+2)
    (hB : Multicover.IsCover B (q+2) 3 1) : familyBound q ≤ Fintype.card ι := by
  classical
  have hv' : Fintype.card α = pointCount q+1 := by simpa [pointCount,Nat.add_assoc] using hv
  unfold familyBound
  by_cases he : ∃ x, indexedDegree B x = pointCount q
  · obtain ⟨x,hx⟩ := he
    exact (Nat.min_le_right _ _).trans (completion_of_exact_link hq ho hv' hB x hx).2
  · by_cases he' : ∃ x, indexedDegree B x = pointCount q+1
    · obtain ⟨x,hx⟩ := he'
      have hw : Fintype.card {p : α // p ∉ ({x} : Finset α)} = pointCount q := by
        rw [Multicover.subset_complement_card,card_singleton,hv']; omega
      have hl : Multicover.IsCover (Multicover.subsetLink B {x}) (q+1) 2 1 := by
        simpa using Multicover.subsetLink_isCover hB {x} (by simp)
      have hc : Fintype.card {i // ({x} : Finset α) ⊆ B i} = pointCount q+1 := by
        rw [Multicover.subsetLink_card,Multicover.subsetDegree_singleton,hx]
      obtain ⟨K,_,hK⟩ := furedi_sane_deletion (by omega) hw hl hc
      exact (Nat.min_le_right _ _).trans (completion_of_link_selection hq ho hv' hB x K hK).2
    · have hd (x : α) : pointCount q+2 ≤ indexedDegree B x := by
        have hl := parent_degree_floor hq hv' hB x
        have h₀ : indexedDegree B x ≠ pointCount q := fun h => he ⟨x,h⟩
        have h₁ : indexedDegree B x ≠ pointCount q+1 := fun h => he' ⟨x,h⟩
        omega
      apply (Nat.min_le_left _ _).trans
      have h := Multicover.bound_of_links (show 0 < q+2 by omega) hB.1
        (fun x => by simpa only [Multicover.subsetLink_card,Multicover.subsetDegree_singleton] using hd x)
      simpa only [hv'] using h

theorem lower_bound {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {C : Family α} (hv : Fintype.card α = q^2+q+2) (hC : IsCover C (q+2) 3) :
    familyBound q ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using indexed_lower_bound hq ho hv
    ((Multicover.ofFamily_isCover_one C (q+2) 3).mpr hC)

theorem indexed_lower_bound_32_7_3 {B : ι → Finset α}
    (hv : Fintype.card α = 32) (hB : Multicover.IsCover B 7 3 1) : 149 ≤ Fintype.card ι := by
  have h := indexed_lower_bound (q := 5) (by decide) (by decide) hv hB
  norm_num [familyBound,pointCount,tripleDemand,capacity,collinearFloor,Schoenheim.ceilDiv,Nat.choose] at h
  exact h

theorem indexed_lower_bound_58_9_3 {B : ι → Finset α}
    (hv : Fintype.card α = 58) (hB : Multicover.IsCover B 9 3 1) : 375 ≤ Fintype.card ι := by
  have h := indexed_lower_bound (q := 7) (by decide) (by decide) hv hB
  norm_num [familyBound,pointCount,tripleDemand,capacity,collinearFloor,Schoenheim.ceilDiv,Nat.choose] at h
  exact h

theorem indexed_lower_bound_92_11_3 {B : ι → Finset α}
    (hv : Fintype.card α = 92) (hB : Multicover.IsCover B 11 3 1) : 774 ≤ Fintype.card ι := by
  have h := indexed_lower_bound (q := 9) (by decide) (by decide) hv hB
  norm_num [familyBound,pointCount,tripleDemand,capacity,collinearFloor,Schoenheim.ceilDiv,Nat.choose] at h
  exact h

theorem lower_bound_32_7_3 {C : Family α} (hv : Fintype.card α = 32)
    (hC : IsCover C 7 3) : 149 ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using indexed_lower_bound_32_7_3 hv
    ((Multicover.ofFamily_isCover_one C 7 3).mpr hC)

theorem lower_bound_58_9_3 {C : Family α} (hv : Fintype.card α = 58)
    (hC : IsCover C 9 3) : 375 ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using indexed_lower_bound_58_9_3 hv
    ((Multicover.ofFamily_isCover_one C 9 3).mpr hC)

theorem lower_bound_92_11_3 {C : Family α} (hv : Fintype.card α = 92)
    (hC : IsCover C 11 3) : 774 ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using indexed_lower_bound_92_11_3 hv
    ((Multicover.ofFamily_isCover_one C 11 3).mpr hC)

/-- Calibration only: the existing stronger order-three result is untouched. -/
theorem calibration_three : familyBound 3 = 39 := by
  norm_num [familyBound,pointCount,tripleDemand,capacity,collinearFloor,Schoenheim.ceilDiv,Nat.choose]

/-- Direct completion form of the full indexed family bound. -/
theorem indexed_completion_lower_bound {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {B : ι → Finset α} (hv : Fintype.card α = q^2+q+2)
    (hB : Multicover.IsCover B (q+2) 3 1) :
    pointCount q + Schoenheim.ceilDiv (tripleDemand q) (capacity q) ≤ Fintype.card ι := by
  simpa only [familyBound_eq_completion hq ho] using indexed_lower_bound hq ho hv hB

/-- Direct completion form for ordinary covering families. -/
theorem completion_lower_bound {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {C : Family α} (hv : Fintype.card α = q^2+q+2) (hC : IsCover C (q+2) 3) :
    pointCount q + Schoenheim.ceilDiv (tripleDemand q) (capacity q) ≤ C.card := by
  simpa only [familyBound_eq_completion hq ho] using lower_bound hq ho hv hC

end CoveringDesigns.ProjectiveLinkBounds
