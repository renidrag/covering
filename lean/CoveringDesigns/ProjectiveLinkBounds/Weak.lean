import CoveringDesigns.ProjectiveLinkBounds.Completion
import CoveringDesigns.Multicover.Family

/-! The weaker family is independent of the deletion theorem. -/
namespace CoveringDesigns.ProjectiveLinkBounds
open Finset Internal

private theorem weak_capacity_gap {q : ℕ} (hq : 5 ≤ q) (ho : Odd q) :
    (pointCount q*(q^2+1)+1)*capacity q < (q+2)*tripleDemand q := by
  have hN := demand_six q
  have hM := capacity_balance (show 3 ≤ q by omega)
  have hC := choose_three_int (q+2)
  have hf := (floor_bounds ho).1
  zify at hN hM hf ⊢
  push_cast at hC
  let D : ℤ := (pointCount q : ℤ)*((q : ℤ)^2+1)+1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hN' := congrArg (fun z : ℤ => 2*((q : ℤ)+2)*z) hN
  have hM' := congrArg (fun z : ℤ => 12*D*z) hM
  have hC' := congrArg (fun z : ℤ => 2*D*z) hC
  have hid : 12*(((q : ℤ)+2)*tripleDemand q-D*capacity q) =
      12*D*collinearFloor q-2*(q : ℤ)*((q : ℤ)+1)*((q : ℤ)+2)*((pointCount q : ℤ)+1) := by
    dsimp [D] at hM' hC' ⊢
    nlinarith
  have hweight := mul_le_mul_of_nonneg_right hf (mul_nonneg (by norm_num : (0 : ℤ) ≤ 3) hD)
  have hq' : (5 : ℤ) ≤ q := by omega
  have hp : 0 < (q : ℤ)^4-3*(q : ℤ)^3-2*(q : ℤ)^2-5*q+6 := by
    have h1 := mul_nonneg (show (0 : ℤ) ≤ q-5 by omega) (pow_nonneg (show (0 : ℤ) ≤ q by omega) 3)
    have h2 := mul_nonneg (show (0 : ℤ) ≤ q-5 by omega) (sq_nonneg (q : ℤ))
    have h3 := mul_nonneg (show (0 : ℤ) ≤ q-1 by omega) (show (0 : ℤ) ≤ q by omega)
    nlinarith
  have hpos := mul_pos (show (0 : ℤ) < q+1 by omega) hp
  have he : 3*((q : ℤ)+1)*D-
      2*(q : ℤ)*((q : ℤ)+1)*((q : ℤ)+2)*((pointCount q : ℤ)+1) =
      ((q : ℤ)+1)*((q : ℤ)^4-3*(q : ℤ)^3-2*(q : ℤ)^2-5*q+6) := by
    dsimp [D,pointCount]
    ring
  change D*capacity q < ((q : ℤ)+2)*tripleDemand q
  nlinarith

private theorem weak_of_completion {q b : ℕ} (hq : 5 ≤ q) (ho : Odd q)
    (hn : pointCount q ≤ b) (hc : tripleDemand q ≤ (b-pointCount q)*capacity q) :
    (pointCount q+1)^2 ≤ (q+2)*b := by
  have hg := weak_capacity_gap hq ho
  by_contra hh
  have hb : (q+2)*b ≤ (pointCount q+1)^2 := by omega
  zify [hn] at hc hg hb ⊢
  have hm := mul_le_mul_of_nonneg_right hb (show (0 : ℤ) ≤ capacity q by positivity)
  have hs := mul_le_mul_of_nonneg_left hc (show (0 : ℤ) ≤ q+2 by omega)
  have he : ((pointCount q : ℤ)+1)^2-((q : ℤ)+2)*pointCount q =
      (pointCount q : ℤ)*((q : ℤ)^2+1)+1 := by
    unfold pointCount
    push_cast
    ring
  have he' := congrArg (fun z : ℤ => z*capacity q) he
  nlinarith

universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

/-- This degree split uses only exact links and parity, with no deletion premise. -/
theorem indexed_weak_lower_bound {q : ℕ} (hq : 5 ≤ q) (ho : Odd q)
    {B : ι → Finset α} (hv : Fintype.card α = q^2+q+2)
    (hB : Multicover.IsCover B (q+2) 3 1) : weakBound q ≤ Fintype.card ι := by
  have hv' : Fintype.card α = pointCount q+1 := by simpa [pointCount,Nat.add_assoc] using hv
  by_cases he : ∃ x, indexedDegree B x = pointCount q
  · obtain ⟨x,hx⟩ := he
    have hc := completion_of_exact_link (by omega) ho hv' hB x hx
    apply (Schoenheim.ceilDiv_le_iff (show 0 < q+2 by omega)).mpr
    exact weak_of_completion hq ho (by omega) hc.1
  · have hd (x : α) : pointCount q+1 ≤ indexedDegree B x := by
      have hl := parent_degree_floor (by omega) hv' hB x
      have hh : indexedDegree B x ≠ pointCount q := fun h => he ⟨x,h⟩
      omega
    have h := Multicover.bound_of_links (show 0 < q+2 by omega) hB.1
      (fun x => by simpa only [Multicover.subsetLink_card,Multicover.subsetDegree_singleton] using hd x)
    simpa only [hv',weakBound,pow_two] using h

theorem weak_lower_bound {q : ℕ} (hq : 5 ≤ q) (ho : Odd q)
    {C : Family α} (hv : Fintype.card α = q^2+q+2) (hC : IsCover C (q+2) 3) :
    weakBound q ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using indexed_weak_lower_bound hq ho hv
    ((Multicover.ofFamily_isCover_one C (q+2) 3).mpr hC)

theorem indexed_weak_bound_32_7_3 {B : ι → Finset α}
    (hv : Fintype.card α = 32) (hB : Multicover.IsCover B 7 3 1) : 147 ≤ Fintype.card ι := by
  have h := indexed_weak_lower_bound (q := 5) (by decide) (by decide) hv hB
  norm_num [weakBound,pointCount,Schoenheim.ceilDiv] at h
  exact h

theorem indexed_weak_bound_58_9_3 {B : ι → Finset α}
    (hv : Fintype.card α = 58) (hB : Multicover.IsCover B 9 3 1) : 374 ≤ Fintype.card ι := by
  have h := indexed_weak_lower_bound (q := 7) (by decide) (by decide) hv hB
  norm_num [weakBound,pointCount,Schoenheim.ceilDiv] at h
  exact h

theorem indexed_weak_bound_92_11_3 {B : ι → Finset α}
    (hv : Fintype.card α = 92) (hB : Multicover.IsCover B 11 3 1) : 770 ≤ Fintype.card ι := by
  have h := indexed_weak_lower_bound (q := 9) (by decide) (by decide) hv hB
  norm_num [weakBound,pointCount,Schoenheim.ceilDiv] at h
  exact h

theorem weak_bound_32_7_3 {C : Family α} (hv : Fintype.card α = 32)
    (hC : IsCover C 7 3) : 147 ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using indexed_weak_bound_32_7_3 hv
    ((Multicover.ofFamily_isCover_one C 7 3).mpr hC)

theorem weak_bound_58_9_3 {C : Family α} (hv : Fintype.card α = 58)
    (hC : IsCover C 9 3) : 374 ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using indexed_weak_bound_58_9_3 hv
    ((Multicover.ofFamily_isCover_one C 9 3).mpr hC)

theorem weak_bound_92_11_3 {C : Family α} (hv : Fintype.card α = 92)
    (hC : IsCover C 11 3) : 770 ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using indexed_weak_bound_92_11_3 hv
    ((Multicover.ofFamily_isCover_one C 11 3).mpr hC)

end CoveringDesigns.ProjectiveLinkBounds
