import CoveringDesigns.HigherIncidence.Counting
import CoveringDesigns.HorsleySingh.Matrices
import CoveringDesigns.Weighted.Matrix

/-! General subset-incidence decomposition and selected-row obstructions.
Horsley–Singh Lemmas 1, 3(a), 5 and 16, for ordinary finite families. -/
namespace CoveringDesigns.HigherIncidence
open Finset Matrix HorsleySingh
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Inclusion from all j-subsets to any selected collection of subsets. -/
def inclusion (j : ℕ) (S : Finset (Finset α)) : Matrix (subsets α j) S ℝ :=
  incidence S (subsets α j)

theorem inclusion_gram_entry (j : ℕ) (S : Finset (Finset α)) (X Y : S) :
    ((inclusion j S).transpose * inclusion j S) X Y =
      ((X.val ∩ Y.val).card.choose j : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, inclusion, incidence]
  rw [sum_coe_sort (subsets α j) (fun U =>
    (if U ⊆ X.val then (1 : ℝ) else 0)*(if U ⊆ Y.val then 1 else 0))]
  have he (U : Finset α) :
      (if U ⊆ X.val then (1 : ℝ) else 0)*(if U ⊆ Y.val then 1 else 0) =
        if U ⊆ X.val ∩ Y.val then 1 else 0 := by
    by_cases hx : U ⊆ X.val <;> by_cases hy : U ⊆ Y.val <;> simp [hx, hy, subset_inter_iff]
  simp_rw [he]
  rw [← sum_filter]
  have hf : (subsets α j).filter (· ⊆ X.val ∩ Y.val) = (X.val ∩ Y.val).powersetCard j := by
    ext U
    simp [mem_powersetCard, and_comm]
  rw [hf]
  simp

def positivePart (s : ℕ) (b : ℕ → ℕ) (S : Finset (Finset α)) : Matrix S S ℝ :=
  ∑ j ∈ range s, (coefficient s b j : ℝ) • ((inclusion j S).transpose * inclusion j S)

theorem positivePart_posSemidef {s : ℕ} {b : ℕ → ℕ}
    (ha : ∀ j < s, 0 ≤ coefficient s b j) (S : Finset (Finset α)) :
    (positivePart s b S).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j hj
  have hg : ((inclusion j S).transpose * inclusion j S).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (inclusion j S)
  exact hg.smul (by exact_mod_cast ha j (mem_range.mp hj))

/-- The positive part has baseline entries off diagonal and the corrected
baseline on the diagonal. This is the general binomial-inversion step. -/
theorem positivePart_entry (s : ℕ) (b : ℕ → ℕ) (S : Finset (Finset α))
    (hS : ∀ X ∈ S, X.card=s) (X Y : S) :
    positivePart s b S X Y = (b (X.val ∪ Y.val).card : ℝ) -
      if X=Y then (coefficient s b s : ℝ) else 0 := by
  have hx := hS X.val X.property
  have hy := hS Y.val Y.property
  have hl : (X.val ∩ Y.val).card ≤ s := by
    simpa [hx] using card_le_card (inter_subset_left (s₁ := X.val) (s₂ := Y.val))
  have hf : (∑ j ∈ range (s+1), (coefficient s b j : ℝ)*(X.val ∩ Y.val).card.choose j) =
      (b (X.val ∪ Y.val).card : ℝ) := by
    rw [union_card hx hy]
    exact_mod_cast coefficient_inversion s b hl
  have ht : ((X.val ∩ Y.val).card.choose s : ℝ) = if X=Y then 1 else 0 := by
    by_cases he : X=Y
    · subst Y; simp [hx]
    · have hn : X.val ≠ Y.val := fun hh => he (Subtype.ext hh)
      simp [he, Nat.choose_eq_zero_of_lt (intersection_lt_of_ne hx hy hn)]
  rw [sum_range_succ, ht] at hf
  have hp : positivePart s b S X Y =
      ∑ j ∈ range s, (coefficient s b j : ℝ)*(X.val ∩ Y.val).card.choose j := by
    simp [positivePart, Matrix.sum_apply, inclusion_gram_entry]
  rw [hp]
  split_ifs at hf ⊢ <;> linarith

def excessMatrix (C : Family α) (b : ℕ → ℕ) (S : Finset (Finset α)) : Matrix S S ℝ :=
  fun X Y => (excess C b X.val Y.val : ℝ)

theorem incidence_gram_eq (C : Family α) (s : ℕ) (b : ℕ → ℕ)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=s) :
    incidence C S * (incidence C S).transpose =
      Matrix.diagonal (fun X : S =>
        ((coefficient s b s + multiplicity C X.val-b s : ℤ) : ℝ)) +
      excessMatrix C b S + positivePart s b S := by
  ext X Y
  rw [HorsleySingh.incidence_gram_entry]
  simp only [Matrix.add_apply, positivePart_entry s b S hS, excessMatrix]
  by_cases he : X=Y
  · subst Y
    simp [excess, hS X.val X.property]
  · have hv : X.val ≠ Y.val := fun hh => he (Subtype.ext hh)
    simp [excess, hv, he]

/-- General weighted selected-subset obstruction (Lemma 16). Its structural
contract needs only coefficient and multiplicity bounds, not coverage. -/
theorem weighted_rank_obstruction {C : Family α} {s : ℕ} {b : ℕ → ℕ}
    (ha : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ multiplicity C Z)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=s)
    (c : S → ℝ) (hc : ∀ X, 0 < c X)
    (hd : ∀ X : S, ∑ Y : S, (excess C b X.val Y.val : ℝ)*c Y <
      ((coefficient s b s + multiplicity C X.val-b s : ℤ) : ℝ)*c X) :
    S.card ≤ C.card := by
  apply Fintype.card_coe S ▸ Fintype.card_coe C ▸
    Weighted.gram_card_le_of_weighted_row_sum_lt (incidence C S)
      (fun X => ((coefficient s b s + multiplicity C X.val-b s : ℤ) : ℝ)) c
      (excessMatrix C b S) (positivePart s b S)
  · intro X Y
    exact congrArg Int.cast (excess_comm C b X.val Y.val)
  · intro X Y
    change (0 : ℝ) ≤ (excess C b X.val Y.val : ℝ)
    exact_mod_cast excess_nonneg hb (hS X.val X.property) (hS Y.val Y.property)
  · exact hc
  · exact hd
  · exact positivePart_posSemidef ha S
  · exact incidence_gram_eq C s b S hS

/-- Lemma 5 is the unit-weight specialisation, including an empty selection. -/
theorem rank_obstruction {C : Family α} {s : ℕ} {b : ℕ → ℕ}
    (ha : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ multiplicity C Z)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=s)
    (hd : ∀ X ∈ S, ∑ Y ∈ S, excess C b X Y <
      coefficient s b s + multiplicity C X-b s) : S.card ≤ C.card := by
  apply weighted_rank_obstruction ha hb S hS (fun _ => 1) (by intro; norm_num)
  intro X
  have hh : (∑ Y ∈ S, (excess C b X.val Y : ℝ)) <
      ((coefficient s b s + multiplicity C X.val-b s : ℤ) : ℝ) := by
    exact_mod_cast hd X.val X.property
  simpa only [mul_one, sum_coe_sort S (fun Y => (excess C b X.val Y : ℝ))] using hh

end CoveringDesigns.HigherIncidence
