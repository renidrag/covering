import CoveringDesigns.Combinatorics.WeightedPartition
import CoveringDesigns.Weighted.Matrix

/-! Minimum-potential partitions followed by strict Gram rank.
Integer weights suffice; empty types and empty parts are permitted.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.Weighted
open Finset Matrix

/-- A bounded nonnegative integral excess can be split into strictly dominated
parts. A largest part suffices; no ranks of overlapping column spaces are added. -/
theorem partitioned_gram_card_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (R : Matrix ι κ ℝ) (w : ι → ι → ℤ) (P : Matrix ι ι ℝ)
    {q : ℕ} (hq : 0 < q) {ρ : ℝ} (hρ : 0 < ρ) {D : ℤ}
    (hs : ∀ x y, w x y = w y x) (hn : ∀ x y, 0 ≤ w x y)
    (hz : ∀ x, w x x = 0) (hd : ∀ x, ∑ y, w x y ≤ D)
    (hstrict : (D : ℝ) < (q : ℝ)*ρ) (hP : P.PosSemidef)
    (hgram : R*R.transpose = Matrix.diagonal (fun _ => ρ) +
      Matrix.of (fun x y => (w x y : ℝ)) + P) :
    Fintype.card ι ≤ q*Fintype.card κ := by
  classical
  obtain ⟨f, hf⟩ := WeightedPartition.exists_balanced_partition hq w hs hz
  obtain ⟨i, hi, _⟩ := WeightedPartition.exists_large_part hq f
  let T := univ.filter (fun x => f x = i)
  let X : Matrix T κ ℝ := fun x j => R x.val j
  let E : Matrix T T ℝ := fun x y => (w x.val y.val : ℝ)
  have hpart (x : T) : (∑ y : T, w x.val y.val) =
      WeightedPartition.classDegree w f x.val (f x.val) := by
    have hx : f x.val = i := (mem_filter.mp x.property).2
    simp only [sum_coe_sort, T, sum_filter, WeightedPartition.classDegree, hx]
  have hrow (x : T) : ∑ y : T, E x y * 1 < ρ*1 := by
    have hb : (q : ℤ)*(∑ y : T, w x.val y.val) ≤ D := by
      rw [hpart]
      exact (hf x.val).trans (hd x.val)
    have hbR : (q : ℝ)*(∑ y : T, E x y) ≤ (D : ℝ) := by
      dsimp only [E]
      exact_mod_cast hb
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    simp only [mul_one]
    nlinarith [hρ]
  have hg : X*X.transpose = Matrix.diagonal (fun _ => ρ) + E +
      P.submatrix Subtype.val Subtype.val := by
    ext x y
    have he := congrFun (congrFun hgram x.val) y.val
    change (∑ j, R x.val j * R y.val j) = _ at he
    change (∑ j, R x.val j * R y.val j) = _
    rw [he]
    change (if x.val=y.val then ρ else 0) + (w x.val y.val : ℝ) + P x.val y.val =
      (if x=y then ρ else 0) + (w x.val y.val : ℝ) + P x.val y.val
    by_cases h : x=y
    · subst y; simp
    · have hv : x.val ≠ y.val := fun h' => h (Subtype.ext h')
      simp [h,hv]
  have hb := gram_card_le_of_weighted_row_sum_lt X (fun _ => ρ) (fun _ => 1)
    E (P.submatrix Subtype.val Subtype.val)
    (fun x y => by dsimp only [E]; exact_mod_cast hs x.val y.val)
    (fun x y => by dsimp only [E]; exact_mod_cast hn x.val y.val)
    (by intro x; norm_num) hrow (hP.submatrix _) hg
  have hc : T.card ≤ Fintype.card κ := by simpa using hb
  exact hi.trans (Nat.mul_le_mul_left q hc)

end CoveringDesigns.Weighted
