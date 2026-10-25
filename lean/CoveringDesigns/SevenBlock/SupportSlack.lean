import CoveringDesigns.Foundations.Intersecting
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Exact dual-support slack. All pairs are pairs of actual indices; equal
supports are never deduplicated. Subtraction and imbalance are in ℤ.
Formalisation: Rob Gardiner, with AI assistance.
-/

namespace CoveringDesigns.SevenBlock
open Finset

private theorem twice_choose_two (n : ℕ) :
    2 * (n.choose 2 : ℤ) = (n : ℤ) * (n - 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    nlinarith

/-- The nonnegativity uses integrality, including negative differences. -/
theorem consecutive_nonneg (z : ℤ) : 0 ≤ z * (z - 1) := by
  by_cases h : z ≤ 0
  · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
  · exact mul_nonneg (by omega) (by omega)

/-- Exact integer imbalance for any finite list of natural counts. The
remainder bound is unnecessary for this algebraic identity. -/
theorem imbalance_identity {ι : Type*} (T : Finset ι) (n : ι → ℕ)
    (A s : ℕ) (htotal : ∑ i ∈ T, n i = T.card * A + s) :
    2 * ((∑ i ∈ T, (n i).choose 2 : ℤ) -
      ((T.card : ℤ) * (A.choose 2 : ℤ) + (s : ℤ) * A)) =
      ∑ i ∈ T, ((n i : ℤ) - A) * ((n i : ℤ) - A - 1) := by
  have hpoly (i : ι) :
      ((n i : ℤ) - A) * ((n i : ℤ) - A - 1) =
        2 * ((n i).choose 2 : ℤ) - 2 * (A : ℤ) * n i + (A : ℤ) * (A + 1) := by
    have := twice_choose_two (n i)
    nlinarith
  simp_rw [hpoly]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  have ht : (∑ i ∈ T, (n i : ℤ)) = (T.card : ℤ) * A + s := by
    exact_mod_cast htotal
  rw [ht]
  simp only [sum_const, nsmul_eq_mul]
  have := twice_choose_two A
  nlinarith

theorem imbalance_nonneg {ι : Type*} (T : Finset ι) (n : ι → ℕ)
    (A s : ℕ) (htotal : ∑ i ∈ T, n i = T.card * A + s) :
    0 ≤ (∑ i ∈ T, (n i).choose 2 : ℤ) -
      ((T.card : ℤ) * (A.choose 2 : ℤ) + (s : ℤ) * A) := by
  have hn : 0 ≤ ∑ i ∈ T, ((n i : ℤ) - A) * ((n i : ℤ) - A - 1) :=
    sum_nonneg fun i _ => consecutive_nonneg _
  rw [← imbalance_identity T n A s htotal] at hn
  omega

variable {X I : Type*} [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]

/-- Excess of common-position incidences over one per actual point pair. -/
def supportExcess (S : X → Finset I) : ℤ :=
  (∑ i, ((indexedDegree S i).choose 2 : ℤ)) -
    ((Fintype.card X).choose 2 : ℤ)

/-- The second common-position moment. -/
def supportMoment (S : X → Finset I) : ℤ :=
  ∑ P ∈ (univ : Finset I).powersetCard 2, ((indexedSubsetDegree S P).choose 2 : ℤ)

/-- Balanced integer second moment, using a quotient and remainder. -/
def balancedMoment (I : Type*) [Fintype I] (A s : ℕ) : ℤ :=
  ((Fintype.card I).choose 2 : ℤ) * (A.choose 2 : ℤ) + (s : ℤ) * A

def supportImbalance (S : X → Finset I) (A s : ℕ) : ℤ :=
  supportMoment S - balancedMoment I A s

/-- Partial overlaps are weighted; identical supports of different points
still contribute to the two moments, but have zero partial-overlap weight. -/
def partialOverlap (S : X → Finset I) (r : ℕ) : ℤ :=
  ∑ P ∈ (univ : Finset X).powersetCard 2,
    ((indexedCommon S P).card - 1 : ℤ) * ((r : ℤ) - (indexedCommon S P).card)

theorem support_excess_eq (S : X → Finset I) :
    supportExcess S = ∑ P ∈ (univ : Finset X).powersetCard 2,
      ((indexedCommon S P).card - 1 : ℤ) := by
  have h := indexedDegree_choose_sum S 2
  have hc : (∑ i, ((indexedDegree S i).choose 2 : ℤ)) =
      ∑ P ∈ (univ : Finset X).powersetCard 2, ((indexedCommon S P).card : ℤ) := by
    exact_mod_cast h
  simp [supportExcess, hc, sum_sub_distrib]

theorem support_moment_eq (S : X → Finset I) :
    supportMoment S = ∑ P ∈ (univ : Finset X).powersetCard 2,
      (((indexedCommon S P).card).choose 2 : ℤ) := by
  unfold supportMoment
  exact_mod_cast indexedSubsetDegree_choose_sum S 2 2

/-- The exact slack identity is algebraic; nonnegativity has separate,
explicit uniformity and intersection hypotheses below. -/
theorem support_slack_identity (S : X → Finset I) (r A s : ℕ) :
    (r : ℤ) * supportExcess S - 2 * balancedMoment I A s =
      partialOverlap S r + 2 * supportImbalance S A s := by
  have hp : partialOverlap S r = (r : ℤ) * supportExcess S - 2 * supportMoment S := by
    rw [support_excess_eq, support_moment_eq]
    simp only [partialOverlap, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro P _
    have := twice_choose_two (indexedCommon S P).card
    nlinarith
  rw [hp, supportImbalance]
  ring

theorem support_imbalance_identity (S : X → Finset I) (r A s : ℕ)
    (hsize : ∀ x, (S x).card = r)
    (hdivision : Fintype.card X * r.choose 2 = (Fintype.card I).choose 2 * A + s) :
    2 * supportImbalance S A s =
      ∑ P ∈ (univ : Finset I).powersetCard 2,
        ((indexedSubsetDegree S P : ℤ) - A) * ((indexedSubsetDegree S P : ℤ) - A - 1) := by
  have ht : ∑ P ∈ (univ : Finset I).powersetCard 2, indexedSubsetDegree S P =
      ((univ : Finset I).powersetCard 2).card * A + s := by
    rw [indexedSubsetDegree_sum]
    simpa [hsize, Nat.mul_comm] using hdivision
  simpa [supportImbalance, supportMoment, balancedMoment] using
    imbalance_identity ((univ : Finset I).powersetCard 2) (indexedSubsetDegree S) A s ht

theorem support_imbalance_nonneg (S : X → Finset I) (r A s : ℕ)
    (hsize : ∀ x, (S x).card = r)
    (hdivision : Fintype.card X * r.choose 2 = (Fintype.card I).choose 2 * A + s) :
    0 ≤ supportImbalance S A s := by
  have hn : 0 ≤ ∑ P ∈ (univ : Finset I).powersetCard 2,
      ((indexedSubsetDegree S P : ℤ) - A) * ((indexedSubsetDegree S P : ℤ) - A - 1) :=
    sum_nonneg fun P _ => consecutive_nonneg _
  rw [← support_imbalance_identity S r A s hsize hdivision] at hn
  omega

private theorem common_bounds (S : X → Finset I) (r : ℕ)
    (hsize : ∀ x, (S x).card = r)
    (hmeet : ∀ x y, x ≠ y → (S x ∩ S y).Nonempty)
    {P : Finset X} (hP : P ∈ (univ : Finset X).powersetCard 2) :
    1 ≤ (indexedCommon S P).card ∧ (indexedCommon S P).card ≤ r := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (mem_powersetCard_univ.mp hP)
  rw [indexedCommon_pair]
  exact ⟨card_pos.mpr (hmeet x y hxy),
    (card_le_card inter_subset_left).trans_eq (hsize x)⟩

theorem partial_overlap_nonneg (S : X → Finset I) (r : ℕ)
    (hsize : ∀ x, (S x).card = r)
    (hmeet : ∀ x y, x ≠ y → (S x ∩ S y).Nonempty) :
    0 ≤ partialOverlap S r := by
  apply sum_nonneg
  intro P hP
  have h := common_bounds S r hsize hmeet hP
  exact mul_nonneg (by omega) (by omega)

/-- At r=3 the partial-overlap sum counts actual unordered point pairs with
two common positions, including their multiplicities as distinct points. -/
theorem partial_overlap_three (S : X → Finset I)
    (hsize : ∀ x, (S x).card = 3)
    (hmeet : ∀ x y, x ≠ y → (S x ∩ S y).Nonempty) :
    partialOverlap S 3 =
      (((univ : Finset X).powersetCard 2).filter
        (fun P => (indexedCommon S P).card = 2)).card := by
  rw [partialOverlap, card_eq_sum_ones, sum_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro P hP
  have h := common_bounds S 3 hsize hmeet hP
  have he : (indexedCommon S P).card = 1 ∨ (indexedCommon S P).card = 2 ∨
      (indexedCommon S P).card = 3 := by omega
  rcases he with he | he | he <;> simp [he]

#guard_standard_axioms consecutive_nonneg imbalance_identity imbalance_nonneg
  support_excess_eq support_moment_eq support_slack_identity support_imbalance_identity
  support_imbalance_nonneg partial_overlap_nonneg partial_overlap_three

end CoveringDesigns.SevenBlock
