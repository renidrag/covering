import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push

/-! Nonnegative integer charges, independent of covering geometry. -/

namespace CoveringDesigns.DeficitCharging
open Finset

variable {α β : Type*}
attribute [local instance] Classical.propDecidable

/-- Every point failing one of the zero-excess conditions costs at least
one unit. Degrees and image coordinates may fail simultaneously. -/
theorem bad_card_le (H : Finset α) (L : Finset β)
    (degreeExcess : α → ℕ) (imageExcess : β → α → ℕ) :
    (H.filter fun y => ¬ (degreeExcess y = 0 ∧
      ∀ x ∈ L, imageExcess x y = 0)).card ≤
      (∑ y ∈ H, degreeExcess y) + ∑ x ∈ L, ∑ y ∈ H, imageExcess x y := by
  classical
  have hp (y : α) :
      (if ¬ (degreeExcess y = 0 ∧ ∀ x ∈ L, imageExcess x y = 0) then 1 else 0) ≤
        degreeExcess y + ∑ x ∈ L, imageExcess x y := by
    by_cases hb : degreeExcess y = 0 ∧ ∀ x ∈ L, imageExcess x y = 0
    · rw [if_neg (not_not_intro hb)]
      omega
    · rw [if_pos hb]
      by_cases hd : degreeExcess y = 0
      · have hx : ∃ x ∈ L, imageExcess x y ≠ 0 := by
          by_contra hn
          push Not at hn
          exact hb ⟨hd, hn⟩
        obtain ⟨x, hx, he⟩ := hx
        have hs := single_le_sum (fun z (_ : z ∈ L) => Nat.zero_le (imageExcess z y)) hx
        omega
      · omega
  have hs := sum_le_sum (s := H) (fun y _ => hp y)
  simpa only [card_eq_sum_ones, sum_filter, sum_add_distrib,
    sum_comm (s := H) (t := L)] using hs

/-- Only positive rows contribute to a bounded nonnegative deficit sum. -/
theorem sum_le_mul_positive (L : Finset β) (δ : β → ℕ) (D : ℕ)
    (hδ : ∀ x ∈ L, δ x ≤ D) :
    (∑ x ∈ L, δ x) ≤ D * (L.filter fun x => 0 < δ x).card := by
  classical
  calc
    _ ≤ ∑ x ∈ L, if 0 < δ x then D else 0 := by
      apply sum_le_sum
      intro x hx
      by_cases hp : 0 < δ x
      · simpa [hp] using hδ x hx
      · simp [hp, Nat.eq_zero_of_not_pos hp]
    _ = _ := by simp [← sum_filter, Nat.mul_comm]

/-- Lower count in subtraction-free form. The selected points are counted,
not their distinct charge or support patterns. -/
theorem regular_count (H : Finset α) (L : Finset β)
    (degreeExcess : α → ℕ) (imageExcess : β → α → ℕ) (D : ℕ)
    (hδ : ∀ x ∈ L, (∑ y ∈ H, imageExcess x y) ≤ D) :
    H.card ≤
      (H.filter fun y => degreeExcess y = 0 ∧
        ∀ x ∈ L, imageExcess x y = 0).card +
      (∑ y ∈ H, degreeExcess y) +
      D * (L.filter fun x => 0 < ∑ y ∈ H, imageExcess x y).card := by
  classical
  have hbad := bad_card_le H L degreeExcess imageExcess
  have hsum := sum_le_mul_positive L (fun x => ∑ y ∈ H, imageExcess x y) D hδ
  have hpartition := card_filter_add_card_filter_not
    (s := H) (p := fun y => degreeExcess y = 0 ∧ ∀ x ∈ L, imageExcess x y = 0)
  omega

end CoveringDesigns.DeficitCharging
