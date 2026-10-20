import CoveringDesigns.TwoKMinusTwoCapacity.Indexed
import CoveringDesigns.AffineCapacity.Boundary

/-!
# Thirteen-occurrence budget at the ordinary endpoints

The budget is reconstructed from general actual-incidence contracts for
k≥14. The established k≥33 theorem is unchanged. The endpoint exclusion
here additionally requires actual triple coverage; no extension of the
indexed threefold pair-cover theorem is asserted.
Formalisation: Rob Gardiner with AI assistance.
-/

namespace CoveringDesigns.SaturatedMatching
open Finset Matrix BoundaryRank BoundaryIncidence AffineCapacity
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] {k : ℕ}

theorem boundary_six (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) :
    (6 : ℝ)*((k : ℝ)-1)-3*((Fintype.card α : ℝ)-1)=6-3 := by
  have hh : Fintype.card α + 2 = 2*k := by omega
  have hR : (Fintype.card α : ℝ)+2=2*(k : ℝ) := by exact_mod_cast hh
  linarith

/-- Exact low-point count, corank budget and regular-point lower count,
with only the range needed for the natural subtraction k-14. -/
theorem thirteen_budget (B : ι → Finset α)
    (hv : Fintype.card α = 2*k-2) (hk : 14 ≤ k)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ indexedSubsetDegree B {x,y})
    (hb : Fintype.card ι = 13) :
    (lowPoints B 6).card = k-14+eta B 6 ∧
    positiveCount B 6 3 + 2*(13-(incidence B 6).rank) + eta B 6 + k ≤ 40 ∧
    1 ≤ 13-(incidence B 6).rank ∧
    4*k+6*(13-(incidence B 6).rank)+eta B 6 ≤ (regularPoints B 6 3).card+108 := by
  have hdeg := TwoKMinusTwoCapacity.indexed_degree_ge_six B hv (by omega) hsize hpair
  have hbound := boundary_six hv (by omega)
  have hcenter : (6 : ℝ)^2 ≤ (Fintype.card ι : ℝ)*3 := by rw [hb]; norm_num
  obtain ⟨_, _, hu, hr⟩ := completion B (by omega) (by norm_num : 3<6)
    hsize hpair hbound hcenter
  have hd := degree_balance B hsize hdeg
  have hw := (incidence B 6).rank_le_card_width
  have hl := lowerCount_le B (by omega) (by norm_num : 3<6)
    hsize hdeg hpair hbound hcenter
  have hv' : Fintype.card α + 2 = 2*k := by omega
  have hvR : (Fintype.card α : ℝ) = 2*(k : ℝ)-2 := by
    have hh : (Fintype.card α : ℝ)+2=2*(k : ℝ) := by exact_mod_cast hv'
    linarith
  rw [hb] at hd hu hw hl
  norm_num only [Nat.reduceAdd] at hd
  have he : (lowPoints B 6).card = k-14+eta B 6 := by omega
  refine ⟨he, by omega, hu, ?_⟩
  unfold lowerCount at hl
  rw [hvR] at hl
  norm_num at hl
  have hLR : (4 : ℝ)*k+6*(13-(incidence B 6).rank : ℕ)+eta B 6 ≤
      (regularPoints B 6 3).card+108 := by nlinarith [hl]
  exact_mod_cast hLR

/-- At k=31,32 each regular support fibre contains at most nine actual
points, including repeated incidence rows. -/
theorem regular_fibre_le_nine (B : ι → Finset α)
    (hv : Fintype.card α = 2*k-2) (hk : 31 ≤ k) (hk' : k ≤ 32)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ indexedSubsetDegree B {x,y})
    (r : ι → ℝ) (hr : r ∈ (regularPoints B 6 3).image (row B)) :
    ((regularPoints B 6 3).filter (fun x => row B x = r)).card ≤ 9 := by
  classical
  have hc := indexed_clone_capacity B
    ((regularPoints B 6 3).filter (fun x => row B x = r)) hsize
    (by
      obtain ⟨x, hx, he⟩ := mem_image.mp hr
      exact ⟨x, mem_filter.mpr ⟨hx,he⟩⟩)
    (fun x hx => regular_degree B 6 3 (mem_filter.mp hx).1)
    (by
      intro x hx y hy i
      exact row_membership_eq B
        ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) i)
    hpair
  have hv' : Fintype.card α + 2 = 2*k := by omega
  norm_num only [Nat.reduceAdd] at hc
  omega

/-- The nonsaturated ordinary endpoint branch. Actual triple coverage is
an explicit premise, in addition to the multiplicity-three floor. -/
theorem no_thirteen_of_pair_floor (B : ι → Finset α)
    (hv : Fintype.card α = 2*k-2) (hk : 31 ≤ k) (hk' : k ≤ 32)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ indexedSubsetDegree B {x,y})
    (hcover : ∀ U : Finset α, U.card = 3 → ∃ i, U ⊆ B i)
    (hb : Fintype.card ι = 13) : False := by
  classical
  obtain ⟨_, hbudget, hu, hlow⟩ := thirteen_budget B hv (by omega) hsize hpair hb
  have hbound := boundary_six hv (by omega)
  have hcenter : (6 : ℝ)^2 ≤ (Fintype.card ι : ℝ)*3 := by rw [hb]; norm_num
  have hd := dimension_le B (by omega) (by norm_num : 3<6) hsize hpair hbound hcenter
  have hs := supports_le B (by omega) (by norm_num : 3<6) hsize hpair hbound hcenter
  rw [hb] at hd hs
  have hf := regular_fibre_le_nine B hv hk hk' hsize hpair
  have hp := card_eq_sum_card_image (row B) (regularPoints B 6 3)
  have hsum := sum_le_sum hf
  simp only [← hp, sum_const, Nat.nsmul_eq_mul] at hsum
  have hu4 : 13-(incidence B 6).rank ≤ 4 := by omega
  by_cases hu2 : 13-(incidence B 6).rank ≤ 2
  · have hexp : 2 ^ (13-(incidence B 6).rank-1) ≤ 2 := by
      have hh : 13-(incidence B 6).rank-1 ≤ 1 := by omega
      have hm := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hh
      simpa using hm
    have hs2 := hs.trans hexp
    have hcard : (regularPoints B 6 3).card ≤ 18 := by omega
    omega
  by_cases hu3 : 13-(incidence B 6).rank = 3
  · have hc := card_le_of_dimension_lt B (regularPoints B 6 3)
      (by omega : 1 ≤ 3) (by omega : 3 ≤ Fintype.card α)
      hcover (fun i => (hsize i).le) (by omega)
    omega
  have huEq : 13-(incidence B 6).rank = 4 := by omega
  have hc := card_le_max_of_fibres B (regularPoints B 6 3)
    (by omega : 1 ≤ 3) (by omega : 3 ≤ Fintype.card α)
    hcover (fun i => (hsize i).le) (by omega) hf
  norm_num at hc
  omega

end CoveringDesigns.SaturatedMatching
