import CoveringDesigns.MulticoverIncidence.Counting
import CoveringDesigns.HigherIncidence.Matrices

/-! Indexed higher-incidence Gram decomposition and weighted rank obstructions.
Columns are occurrence indices, without any injectivity hypothesis. -/
namespace CoveringDesigns.MulticoverIncidence
open Finset Matrix HigherIncidence
universe u v
variable {α : Type u} {ι : Type v} [DecidableEq α] [Fintype ι]

def incidence (B : ι → Finset α) (S : Finset (Finset α)) : Matrix S ι ℝ :=
  fun X i => if X.val ⊆ B i then 1 else 0

theorem incidence_gram_entry (B : ι → Finset α) (S : Finset (Finset α)) (X Y : S) :
    (incidence B S * (incidence B S).transpose) X Y =
      (indexedSubsetDegree B (X.val ∪ Y.val) : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidence, indexedSubsetDegree,
    card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply sum_congr rfl
  intro i _
  by_cases hx : X.val ⊆ B i <;> by_cases hy : Y.val ⊆ B i <;>
    simp [hx, hy, union_subset_iff]

theorem incidence_gram_rank_le (B : ι → Finset α) (S : Finset (Finset α)) :
    (incidence B S * (incidence B S).transpose).rank ≤ Fintype.card ι :=
  (Matrix.rank_mul_le_left (incidence B S) (incidence B S).transpose).trans
    (incidence B S).rank_le_card_width

variable [Fintype α]

def excessMatrix (B : ι → Finset α) (b : ℕ → ℕ) (S : Finset (Finset α)) : Matrix S S ℝ :=
  fun X Y => (excess B b X.val Y.val : ℝ)

theorem incidence_gram_eq (B : ι → Finset α) (s : ℕ) (b : ℕ → ℕ)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=s) :
    incidence B S * (incidence B S).transpose =
      Matrix.diagonal (fun X : S =>
        ((coefficient s b s + indexedSubsetDegree B X.val-b s : ℤ) : ℝ)) +
      excessMatrix B b S + positivePart s b S := by
  ext X Y
  rw [incidence_gram_entry]
  simp only [Matrix.add_apply, positivePart_entry s b S hS, excessMatrix]
  by_cases he : X=Y
  · subst Y
    simp [excess, hS X.val X.property]
  · have hv : X.val ≠ Y.val := fun hh => he (Subtype.ext hh)
    simp [excess, hv, he]

/-- General weighted selected-subset obstruction (Lemma 16). Its structural
contract needs only coefficient and multiplicity bounds, not coverage. -/
theorem weighted_rank_obstruction {B : ι → Finset α} {s : ℕ} {b : ℕ → ℕ}
    (ha : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=s)
    (c : S → ℝ) (hc : ∀ X, 0 < c X)
    (hd : ∀ X : S, ∑ Y : S, (excess B b X.val Y.val : ℝ)*c Y <
      ((coefficient s b s + indexedSubsetDegree B X.val-b s : ℤ) : ℝ)*c X) :
    S.card ≤ Fintype.card ι := by
  apply Fintype.card_coe S ▸
    Weighted.gram_card_le_of_weighted_row_sum_lt (incidence B S)
      (fun X => ((coefficient s b s + indexedSubsetDegree B X.val-b s : ℤ) : ℝ)) c
      (excessMatrix B b S) (positivePart s b S)
  · intro X Y
    exact congrArg Int.cast (excess_comm B b X.val Y.val)
  · intro X Y
    change (0 : ℝ) ≤ (excess B b X.val Y.val : ℝ)
    exact_mod_cast excess_nonneg hb (hS X.val X.property) (hS Y.val Y.property)
  · exact hc
  · exact hd
  · exact positivePart_posSemidef ha S
  · exact incidence_gram_eq B s b S hS

/-- Lemma 5 is the unit-weight specialisation, including an empty selection. -/
theorem rank_obstruction {B : ι → Finset α} {s : ℕ} {b : ℕ → ℕ}
    (ha : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=s)
    (hd : ∀ X ∈ S, ∑ Y ∈ S, excess B b X Y <
      coefficient s b s + indexedSubsetDegree B X-b s) : S.card ≤ Fintype.card ι := by
  apply weighted_rank_obstruction ha hb S hS (fun _ => 1) (by intro; norm_num)
  intro X
  have hh : (∑ Y ∈ S, (excess B b X.val Y : ℝ)) <
      ((coefficient s b s + indexedSubsetDegree B X.val-b s : ℤ) : ℝ) := by
    exact_mod_cast hd X.val X.property
  simpa only [mul_one, sum_coe_sort S (fun Y => (excess B b X.val Y : ℝ))] using hh

end CoveringDesigns.MulticoverIncidence
