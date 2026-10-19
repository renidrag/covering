import CoveringDesigns.HorsleySingh.Counting
import CoveringDesigns.Horsley.Matrix
import Mathlib.Algebra.Order.Star.Real

/-! Pair-incidence Gram matrices and the s = 2 case of Lemma 5. -/

namespace CoveringDesigns.HorsleySingh

open Finset Matrix
variable {α : Type*} [DecidableEq α]

/-- Rows are selected subsets; columns are the actual blocks. -/
def incidence (C : Family α) (S : Finset (Finset α)) : Matrix S C ℝ :=
  fun X B => if X.val ⊆ B.val then 1 else 0

/-- Lemma 1(i), valid for any selected subsets, not just pairs. -/
theorem incidence_gram_entry (C : Family α) (S : Finset (Finset α)) (X Y : S) :
    (incidence C S * (incidence C S).transpose) X Y =
      (multiplicity C (X.val ∪ Y.val) : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidence, multiplicity,
    card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_coe_sort C (fun B =>
    (if X.val ⊆ B then (1 : ℝ) else 0) * (if Y.val ⊆ B then 1 else 0))]
  apply sum_congr rfl
  intro B _
  by_cases hX : X.val ⊆ B <;> by_cases hY : Y.val ⊆ B <;>
    simp [hX, hY, union_subset_iff]

/-- Lemma 1(ii): the number of blocks bounds the Gram rank. -/
theorem incidence_gram_rank_le (C : Family α) (S : Finset (Finset α)) :
    (incidence C S * (incidence C S).transpose).rank ≤ C.card := by
  simpa only [Fintype.card_coe] using
    (Matrix.rank_mul_le_left (incidence C S) (incidence C S).transpose).trans
      (incidence C S).rank_le_card_width

/-- Point-versus-selected-subset incidence. -/
def pointPair (S : Finset (Finset α)) : Matrix α S ℝ :=
  fun p X => if p ∈ X.val then 1 else 0

theorem pointPair_gram_entry [Fintype α] (S : Finset (Finset α)) (X Y : S) :
    ((pointPair S).transpose * pointPair S) X Y = ((X.val ∩ Y.val).card : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pointPair]
  calc
    _ = ∑ p : α, if p ∈ X.val ∩ Y.val then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro p _
      by_cases hx : p ∈ X.val <;> by_cases hy : p ∈ Y.val <;> simp [hx, hy]
    _ = _ := by
      have he : (univ : Finset α).filter (fun p => p ∈ X.val ∩ Y.val) = X.val ∩ Y.val := by
        ext p
        simp
      rw [← sum_filter, he]
      simp

/-- Lemma 3(a): the two nonnegative Gram terms for s = 2. -/
def positivePart [Fintype α] (b₃ b₄ : ℕ) (S : Finset (Finset α)) : Matrix S S ℝ :=
  (b₄ : ℝ) • Matrix.of (fun _ _ => 1) +
    ((b₃ : ℝ) - b₄) • ((pointPair S).transpose * pointPair S)

theorem positivePart_entry [Fintype α] (b₃ b₄ : ℕ)
    (S : Finset (Finset α)) (X Y : S) :
    positivePart b₃ b₄ S X Y = (baseline b₃ b₄ X.val Y.val : ℝ) := by
  simp [positivePart, pointPair_gram_entry, baseline]

theorem positivePart_posSemidef [Fintype α] {b₃ b₄ : ℕ} (h₄₃ : b₄ ≤ b₃)
    (S : Finset (Finset α)) : (positivePart b₃ b₄ S).PosSemidef := by
  have hq : ((pointPair S).transpose * pointPair S).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (pointPair S)
  exact (Horsley.ones_posSemidef.smul (Nat.cast_nonneg b₄)).add
    (hq.smul (sub_nonneg.mpr (by exact_mod_cast h₄₃)))

/-- The off-diagonal integer excess embedded in the reals. -/
def excessMatrix (C : Family α) (b₃ b₄ : ℕ) (S : Finset (Finset α)) : Matrix S S ℝ :=
  fun X Y => (excess C b₃ b₄ X.val Y.val : ℝ)

/-- Lemma 3's decomposition on any selected pair set. -/
theorem incidence_gram_eq [Fintype α] (C : Family α) (b₂ b₃ b₄ : ℕ)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card = 2) :
    incidence C S * (incidence C S).transpose =
      Matrix.diagonal (fun X : S =>
        ((diagonal b₂ b₃ b₄ + multiplicity C X.val - b₂ : ℤ) : ℝ)) +
        excessMatrix C b₃ b₄ S + positivePart b₃ b₄ S := by
  ext X Y
  rw [incidence_gram_entry]
  simp only [Matrix.add_apply, positivePart_entry, excessMatrix]
  by_cases he : X = Y
  · subst Y
    simp [excess, baseline, diagonal, hS X.val X.property]
    ring
  · have hv : X.val ≠ Y.val := fun h => he (Subtype.ext h)
    simp [Matrix.diagonal_apply_ne _ he, excess, hv]

/-- Lemma 5 for arbitrary selected pairs. Strict row dominance is the only
selection condition. Uniformity, coverage and nonemptiness are not assumed;
the required triple and quadruple multiplicity bounds are explicit. -/
theorem incidence_rank_obstruction [Fintype α] {C : Family α} {b₂ b₃ b₄ : ℕ}
    (h₄₃ : b₄ ≤ b₃)
    (h₃ : ∀ X : Finset α, X.card = 3 → b₃ ≤ multiplicity C X)
    (h₄ : ∀ X : Finset α, X.card = 4 → b₄ ≤ multiplicity C X)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card = 2)
    (hs : ∀ X ∈ S, ∑ Y ∈ S, excess C b₃ b₄ X Y <
      diagonal b₂ b₃ b₄ + multiplicity C X - b₂) :
    S.card ≤ C.card := by
  have hpd : (Matrix.diagonal (fun X : S =>
      ((diagonal b₂ b₃ b₄ + multiplicity C X.val - b₂ : ℤ) : ℝ)) +
      excessMatrix C b₃ b₄ S).PosDef := by
    apply Horsley.diagonal_add_posDef_of_row_sum_lt
    · intro X Y
      exact congrArg Int.cast (excess_comm C b₃ b₄ X.val Y.val)
    · intro X Y
      change (0 : ℝ) ≤ (excess C b₃ b₄ X.val Y.val : ℝ)
      exact_mod_cast excess_nonneg h₃ h₄ (hS X.val X.property) (hS Y.val Y.property)
    · intro X
      have hh := hs X.val X.property
      have hr : (∑ Y ∈ S, (excess C b₃ b₄ X.val Y : ℝ)) <
          ((diagonal b₂ b₃ b₄ + multiplicity C X.val - b₂ : ℤ) : ℝ) := by
        exact_mod_cast hh
      simpa only [excessMatrix, sum_coe_sort S (fun Y =>
        (excess C b₃ b₄ X.val Y : ℝ))] using hr
  have hg : (incidence C S * (incidence C S).transpose).PosDef := by
    rw [incidence_gram_eq C b₂ b₃ b₄ S hS]
    exact hpd.add_posSemidef (positivePart_posSemidef h₄₃ S)
  simpa only [Fintype.card_coe] using Horsley.card_le_of_gram_posDef (incidence C S) hg

end CoveringDesigns.HorsleySingh
