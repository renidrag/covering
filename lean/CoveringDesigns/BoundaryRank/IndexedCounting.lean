import CoveringDesigns.BoundaryRank.IndexedIncidence
import CoveringDesigns.BoundaryRank.DeficitCharging

/-! Integer charges and the full signed rank-slack lower count. -/
namespace CoveringDesigns.BoundaryIncidence
open Finset Matrix BoundaryRank
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]

/-- Every positive low deficit is bounded by the boundary diagonal. -/
theorem deficit_le (B : ι → Finset α) {k r lam : ℕ}
    (hlr : lam < r) (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (x : Low B r) : deficit B r lam x ≤ r-lam := by
  have hb := balance B hsize hpair hboundary x
  have hn : 0 ≤ ∑ y, excessMatrix B r lam x y :=
    sum_nonneg fun y _ => Nat.cast_nonneg _
  have hd : (deficit B r lam x : ℝ) ≤ ((r-lam : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : lam ≤ r)]
    linarith
  exact_mod_cast hd

/-- The two sorts of integer failures may overlap; every bad point is
still charged at least once. No supports are deduplicated. -/
theorem regular_count (B : ι → Finset α) {k r lam : ℕ}
    (hlr : lam < r) (hsize : ∀ i, (B i).card = k)
    (hdeg : ∀ x, r ≤ indexedDegree B x)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam) :
    (highPoints B r).card ≤ (regularPoints B r lam).card +
      eta B r + (r-lam) * positiveCount B r lam := by
  classical
  have hp (y : α) (hy : y ∈ highPoints B r) :
      (indexedDegree B y - (r+1) = 0 ∧
        ∀ x : Low B r, excess B lam x.val y = 0) ↔
      (indexedDegree B y = r+1 ∧
        ∀ x : Low B r, indexedSubsetDegree B {x.val,y} = lam) := by
    have hd := high_degree B r hdeg hy
    have he (x : Low B r) :
        excess B lam x.val y = 0 ↔ indexedSubsetDegree B {x.val,y} = lam := by
      have hne := low_ne_high B r x hy
      have hf := hpair x.val y hne
      simp only [excess, if_neg hne]
      omega
    simp_rw [he]
    exact and_congr (by omega) Iff.rfl
  have hc := DeficitCharging.regular_count (highPoints B r)
    (univ : Finset (Low B r)) (fun y => indexedDegree B y - (r+1))
    (fun x y => excess B lam x.val y) (r-lam)
    (fun x _ => deficit_le B hlr hsize hpair hboundary x)
  apply hc.trans
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply card_le_card
  intro y hy
  simp only [mem_filter] at hy
  obtain ⟨hy, he⟩ := hy
  apply mem_filter.mpr
  exact ⟨hy, (hp y hy).mp ⟨he.1, fun x => he.2 x (mem_univ x)⟩⟩

/-- The signed lower expression from the general boundary theorem.
In particular `(r-lam-2)*eta` is a real product with its original sign. -/
def lowerCount (v b k r lam η u : ℕ) : ℝ :=
  (1 + ((r : ℝ)-lam-1)*(r+1))*v -
    (((r : ℝ)-lam-1)*k + 2*((r : ℝ)-lam))*b +
    ((r : ℝ)-lam-2)*η + 2*((r : ℝ)-lam)*u

/-- General boundary-to-selection count, with actual rank retained.
No rank or selection conclusion is a premise. -/
theorem lowerCount_le (B : ι → Finset α) {k r lam : ℕ}
    (hb : 0 < Fintype.card ι) (hlr : lam < r)
    (hsize : ∀ i, (B i).card = k)
    (hdeg : ∀ x, r ≤ indexedDegree B x)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (hcenter : (r : ℝ)^2 ≤ (Fintype.card ι : ℝ) * lam) :
    lowerCount (Fintype.card α) (Fintype.card ι) k r lam
      (eta B r) (Fintype.card ι - (incidence B r).rank) ≤
        (regularPoints B r lam).card := by
  obtain ⟨_, _, _, hrank⟩ := completion B hb hlr hsize hpair hboundary hcenter
  have hd := degree_balance B hsize hdeg
  have hc := regular_count B hlr hsize hdeg hpair hboundary
  have hpart : (highPoints B r).card + (lowPoints B r).card = Fintype.card α := by
    rw [highPoints, card_sdiff, inter_univ,
      Nat.sub_add_cancel (card_le_card (subset_univ (lowPoints B r))), card_univ]
  have hw : (incidence B r).rank ≤ Fintype.card ι :=
    (incidence B r).rank_le_card_width
  have hu : (Fintype.card ι - (incidence B r).rank : ℕ) +
      (incidence B r).rank = Fintype.card ι := Nat.sub_add_cancel hw
  have hdR : (k : ℝ)*Fintype.card ι + (lowPoints B r).card =
      (r+1)*Fintype.card α + eta B r := by exact_mod_cast hd
  have hcR : ((highPoints B r).card : ℝ) ≤ (regularPoints B r lam).card +
      eta B r + ((r : ℝ)-lam)*positiveCount B r lam := by
    have hcast : ((r-lam : ℕ) : ℝ) = (r : ℝ)-lam := Nat.cast_sub (by omega)
    have hh : ((highPoints B r).card : ℝ) ≤
      (regularPoints B r lam).card + eta B r +
        ((r-lam : ℕ) : ℝ)*positiveCount B r lam := by exact_mod_cast hc
    rwa [hcast] at hh
  have hpR : ((highPoints B r).card : ℝ) + (lowPoints B r).card = Fintype.card α := by
    exact_mod_cast hpart
  have hrR : ((lowPoints B r).card : ℝ) + positiveCount B r lam ≤
      2 * (incidence B r).rank := by exact_mod_cast hrank
  have huR : ((Fintype.card ι - (incidence B r).rank : ℕ) : ℝ) +
      (incidence B r).rank = Fintype.card ι := by exact_mod_cast hu
  have hρ : 0 ≤ (r : ℝ)-lam := sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt hlr)
  have hprod := mul_le_mul_of_nonneg_left hrR hρ
  unfold lowerCount
  nlinarith [hprod]

end CoveringDesigns.BoundaryIncidence
