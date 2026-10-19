import CoveringDesigns.HorsleySingh.SubsetLinks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Pair counting and the integer row identity in Horsley–Singh Lemma 3. -/

namespace CoveringDesigns.HorsleySingh

open Finset
variable {α : Type*} [DecidableEq α]

/-- The diagonal coefficient `a₂`, with signed subtraction. -/
def diagonal (b₂ b₃ b₄ : ℕ) : ℤ := (b₂ : ℤ) - 2*b₃ + b₄

/-- The paper's `d`, with signed subtraction throughout. -/
def defect (v k b₂ b₃ b₄ : ℕ) : ℤ :=
  (b₂ : ℤ) * ((k.choose 2 : ℤ) - 1) -
    ((v-2).choose 2 : ℤ)*b₄ - 2*(v-2 : ℕ)*b₃

/-- All pairs of the ambient finite point type. -/
def pairs (α : Type*) [Fintype α] : Finset (Finset α) := univ.powersetCard 2

omit [DecidableEq α] in
@[simp] theorem mem_pairs [Fintype α] {X : Finset α} : X ∈ pairs α ↔ X.card = 2 :=
  mem_powersetCard_univ

omit [DecidableEq α] in
@[simp] theorem card_pairs [Fintype α] : (pairs α).card = (Fintype.card α).choose 2 := by
  simp [pairs]

/-- The off-diagonal baseline, extended to the diagonal by the Gram formula. -/
def baseline (b₃ b₄ : ℕ) (X Y : Finset α) : ℤ :=
  (b₄ : ℤ) + ((b₃ : ℤ) - b₄) * (X ∩ Y).card

/-- Off-diagonal excess. It is an integer until its nonnegativity is proved. -/
def excess (C : Family α) (b₃ b₄ : ℕ) (X Y : Finset α) : ℤ :=
  if X = Y then 0 else (multiplicity C (X ∪ Y) : ℤ) - baseline b₃ b₄ X Y

theorem pair_intersection_cases {X Y : Finset α} (hX : X.card = 2)
    (hY : Y.card = 2) (hne : X ≠ Y) :
    ((X ∩ Y).card = 0 ∧ (X ∪ Y).card = 4) ∨
    ((X ∩ Y).card = 1 ∧ (X ∪ Y).card = 3) := by
  have hi := card_le_card (inter_subset_left (s₁ := X) (s₂ := Y))
  have hu := card_union_add_card_inter X Y
  have hlt : (X ∩ Y).card < 2 := by
    by_contra hh
    have he : X ∩ Y = X := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hsub : X ⊆ Y := by rw [← he]; exact inter_subset_right
    exact hne (eq_of_subset_of_card_le hsub (by omega))
  omega

theorem baseline_of_distinct_pairs (b₃ b₄ : ℕ) {X Y : Finset α}
    (hX : X.card = 2) (hY : Y.card = 2) (hne : X ≠ Y) :
    baseline b₃ b₄ X Y = if (X ∪ Y).card = 3 then (b₃ : ℤ) else b₄ := by
  rcases pair_intersection_cases hX hY hne with ⟨hi, hu⟩ | ⟨hi, hu⟩ <;>
    simp [baseline, hi, hu]

theorem baseline_self (b₂ b₃ b₄ : ℕ) {X : Finset α} (hX : X.card = 2) :
    baseline b₃ b₄ X X = (b₂ : ℤ) - diagonal b₂ b₃ b₄ := by
  simp [baseline, diagonal, hX]
  ring

theorem diagonal_entry_nonneg {C : Family α} {b₂ b₃ b₄ : ℕ}
    (ha : 0 ≤ diagonal b₂ b₃ b₄) {X : Finset α} (hX : b₂ ≤ multiplicity C X) :
    0 ≤ diagonal b₂ b₃ b₄ + multiplicity C X - b₂ := by omega

theorem excess_comm (C : Family α) (b₃ b₄ : ℕ) (X Y : Finset α) :
    excess C b₃ b₄ X Y = excess C b₃ b₄ Y X := by
  simp only [excess, baseline, union_comm X Y, inter_comm X Y, eq_comm]

theorem excess_nonneg {C : Family α} {b₃ b₄ : ℕ}
    (h₃ : ∀ X : Finset α, X.card = 3 → b₃ ≤ multiplicity C X)
    (h₄ : ∀ X : Finset α, X.card = 4 → b₄ ≤ multiplicity C X)
    {X Y : Finset α} (hX : X.card = 2) (hY : Y.card = 2) :
    0 ≤ excess C b₃ b₄ X Y := by
  by_cases he : X = Y
  · simp [excess, he]
  · rcases pair_intersection_cases hX hY he with ⟨hi, hu⟩ | ⟨hi, hu⟩
    · have hh : (b₄ : ℤ) ≤ multiplicity C (X ∪ Y) := by exact_mod_cast h₄ _ hu
      simp only [excess, ite_eq_right he, baseline, hi, Nat.cast_zero, mul_zero, add_zero]
      omega
    · have hh : (b₃ : ℤ) ≤ multiplicity C (X ∪ Y) := by exact_mod_cast h₃ _ hu
      simp only [excess, ite_eq_right he, baseline, hi, Nat.cast_one, mul_one]
      omega

theorem multiplicity_sum [Fintype α] (C : Family α) (i : ℕ) :
    ∑ X ∈ univ.powersetCard i, multiplicity C X = ∑ B ∈ C, B.card.choose i := by
  simp_rw [multiplicity_eq_indexed]
  rw [indexedSubsetDegree_sum]
  exact sum_coe_sort C (fun B => B.card.choose i)

theorem multiplicity_pair_sum [Fintype α] {C : Family α} {k : ℕ}
    (hu : Uniform C k) :
    ∑ X ∈ pairs α, multiplicity C X = k.choose 2 * C.card := by
  rw [pairs, multiplicity_sum, sum_const_nat (fun B hB => congrArg (fun n => n.choose 2) (hu B hB))]
  exact Nat.mul_comm _ _

theorem union_multiplicity_sum [Fintype α] {C : Family α} {k : ℕ}
    (hu : Uniform C k) (X : Finset α) :
    ∑ Y ∈ pairs α, multiplicity C (X ∪ Y) = k.choose 2 * multiplicity C X := by
  have he (Y : Finset α) : multiplicity C (X ∪ Y) =
      multiplicity (C.filter (X ⊆ ·)) Y := by
    unfold multiplicity
    congr 1
    ext B
    simp [union_subset_iff, and_assoc]
  simp_rw [he]
  exact multiplicity_pair_sum (fun B hB => hu B (mem_filter.mp hB).1)

/-- Count a point of `X` incident to an ambient pair, in either order. -/
theorem pair_intersection_sum [Fintype α] (X : Finset α) :
    ∑ Y ∈ pairs α, (X ∩ Y).card = X.card * (Fintype.card α - 1) := by
  have hi (Y : Finset α) : (X ∩ Y).card = ∑ p ∈ X, if p ∈ Y then 1 else 0 := by
    rw [← sum_filter, ← card_eq_sum_ones]
    congr 1
  simp_rw [hi]
  rw [sum_comm]
  have hp (p : α) : (∑ Y ∈ pairs α, if p ∈ Y then 1 else 0) = Fintype.card α - 1 := by
    rw [← sum_filter, ← card_eq_sum_ones]
    have he : (pairs α).filter (p ∈ ·) =
        (univ.powersetCard 2).filter ({p} ⊆ ·) := by ext Y; simp [pairs]
    rw [he, card_filter_powersetCard_subset {p} univ 2 (subset_univ _) (by simp)]
    simp
  simp_rw [hp]
  simp

/-- The pair count after removing two points, as an additive identity. -/
theorem choose_two_step {n : ℕ} (hn : 2 ≤ n) :
    (n.choose 2 : ℤ) = ((n-2).choose 2 : ℤ) + 2*(n-2 : ℕ) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp [Nat.add_comm 2, Nat.choose_succ_succ, Nat.choose_one_right]
  omega

/-- Lemma 3(b), stated with signed differences; no truncation is involved. -/
theorem excess_row_sum [Fintype α] {C : Family α} {k b₂ b₃ b₄ : ℕ}
    (hu : Uniform C k) {X : Finset α} (hX : X.card = 2) :
    ∑ Y ∈ pairs α, excess C b₃ b₄ X Y =
      ((multiplicity C X : ℤ) - b₂) * ((k.choose 2 : ℤ)-1) +
        defect (Fintype.card α) k b₂ b₃ b₄ := by
  have hmem : X ∈ pairs α := mem_pairs.mpr hX
  have hv : 2 ≤ Fintype.card α := by
    simpa only [hX, card_univ] using card_le_card (subset_univ X)
  have hcount : (∑ Y ∈ pairs α, (multiplicity C (X ∪ Y) : ℤ)) =
      (k.choose 2 : ℤ) * multiplicity C X := by exact_mod_cast union_multiplicity_sum hu X
  have hint : (∑ Y ∈ pairs α, ((X ∩ Y).card : ℤ)) =
      2 * (Fintype.card α - 1 : ℕ) := by
    exact_mod_cast (pair_intersection_sum X).trans (by rw [hX])
  have hbase : (∑ Y ∈ pairs α, baseline b₃ b₄ X Y) =
      ((Fintype.card α).choose 2 : ℤ)*b₄ +
        ((b₃ : ℤ)-b₄)*(2*(Fintype.card α - 1 : ℕ)) := by
    simp only [baseline, sum_add_distrib, ← mul_sum, hint, sum_const,
      card_pairs, nsmul_eq_mul]
  have he : (∑ Y ∈ pairs α, (multiplicity C (X ∪ Y) : ℤ)) =
      (∑ Y ∈ pairs α, excess C b₃ b₄ X Y) +
      (∑ Y ∈ pairs α, baseline b₃ b₄ X Y) +
      ((multiplicity C X : ℤ) - (2*b₃-b₄)) := by
    have hi (Y : Finset α) : (multiplicity C (X ∪ Y) : ℤ) =
        excess C b₃ b₄ X Y + baseline b₃ b₄ X Y +
          if Y = X then (multiplicity C X : ℤ) - (2*b₃-b₄) else 0 := by
      by_cases hh : X = Y
      · subst Y
        simp [excess, baseline, hX]
        ring
      · simp [excess, hh, Ne.symm hh]
    simp_rw [hi, sum_add_distrib]
    simp [hmem]
  rw [hcount, hbase] at he
  have hc := choose_two_step hv
  have hv' : (Fintype.card α - 1 : ℕ) = (Fintype.card α - 2) + 1 := by omega
  rw [hv', Nat.cast_add, Nat.cast_one] at he
  unfold defect
  rw [hc] at he
  nlinarith [he]

end CoveringDesigns.HorsleySingh
