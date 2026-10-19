import CoveringDesigns.Multicover.Counting
import CoveringDesigns.HigherIncidence.Counting

/-! Occurrence-preserving double counts and signed excess, for any subset size. -/
namespace CoveringDesigns.MulticoverIncidence
open Finset HigherIncidence
universe u v
variable {α : Type u} {ι : Type v} [DecidableEq α] [Fintype ι]

theorem multiplicity_sum [Fintype α] {B : ι → Finset α} {k : ℕ}
    (hu : Multicover.Uniform B k) (s : ℕ) :
    ∑ X ∈ subsets α s, indexedSubsetDegree B X = k.choose s*Fintype.card ι :=
  Multicover.subsetDegree_sum_of_uniform hu s

/-- Each containing occurrence contributes exactly choose(k,s), even when
several occurrence indices carry the same block. -/
theorem union_multiplicity_sum [Fintype α] {B : ι → Finset α} {k : ℕ}
    (hu : Multicover.Uniform B k) (s : ℕ) (X : Finset α) :
    ∑ Y ∈ subsets α s, indexedSubsetDegree B (X ∪ Y) =
      k.choose s*indexedSubsetDegree B X := by
  classical
  simp only [indexedSubsetDegree, card_eq_sum_ones, sum_filter]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro i _
  by_cases hx : X ⊆ B i
  · simp only [union_subset_iff, hx, true_and, ite_true, mul_one]
    rw [← sum_filter, ← card_eq_sum_ones]
    have he : (subsets α s).filter (· ⊆ B i) = (B i).powersetCard s := by
      ext Y
      simp [subsets, mem_powersetCard, and_comm]
    rw [he, card_powersetCard, hu]
  · simp [union_subset_iff, hx]

def excess (B : ι → Finset α) (b : ℕ → ℕ) (X Y : Finset α) : ℤ :=
  if X=Y then 0 else (indexedSubsetDegree B (X ∪ Y) : ℤ)-b (X ∪ Y).card

theorem excess_comm (B : ι → Finset α) (b : ℕ → ℕ) (X Y : Finset α) :
    excess B b X Y = excess B b Y X := by simp only [excess, union_comm X Y, eq_comm]

theorem excess_nonneg {B : ι → Finset α} {b : ℕ → ℕ} {s : ℕ}
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    {X Y : Finset α} (hX : X.card=s) (hY : Y.card=s) : 0 ≤ excess B b X Y := by
  by_cases he : X=Y
  · simp [excess, he]
  · have hlo : s ≤ (X ∪ Y).card := by simpa [hX] using card_le_card (subset_union_left (s₁ := X) (s₂ := Y))
    have hhi : (X ∪ Y).card ≤ 2*s := by have := card_union_le X Y; omega
    have := hb (X ∪ Y) hlo hhi
    simp only [excess, ite_eq_right he]
    omega

/-- The exact signed excess row identity. Uniformity is its only family
hypothesis; coverage and lower bounds are not needed for this equality. -/
theorem excess_row_sum [Fintype α] {B : ι → Finset α} {k s : ℕ}
    (hu : Multicover.Uniform B k) (b : ℕ → ℕ) {X : Finset α} (hX : X.card=s) :
    ∑ Y ∈ subsets α s, excess B b X Y =
      ((indexedSubsetDegree B X : ℤ)-b s)*((k.choose s : ℤ)-1)+
        defect (Fintype.card α) k s b := by
  have hmem : X ∈ subsets α s := mem_subsets.mpr hX
  have hc : (∑ Y ∈ subsets α s, (indexedSubsetDegree B (X ∪ Y) : ℤ)) =
      (k.choose s : ℤ)*indexedSubsetDegree B X := by exact_mod_cast union_multiplicity_sum hu s X
  have hd : (∑ Y ∈ (subsets α s).erase X, (indexedSubsetDegree B (X ∪ Y) : ℤ)) =
      (k.choose s : ℤ)*indexedSubsetDegree B X-indexedSubsetDegree B X := by
    have hh := sum_erase_add (s := subsets α s)
      (f := fun Y => (indexedSubsetDegree B (X ∪ Y) : ℤ)) hmem
    rw [hc, union_self] at hh
    linarith
  have he : (∑ Y ∈ subsets α s, excess B b X Y) =
      (∑ Y ∈ (subsets α s).erase X, (indexedSubsetDegree B (X ∪ Y) : ℤ)) -
      (∑ Y ∈ (subsets α s).erase X, (b (X ∪ Y).card : ℤ)) := by
    rw [← sum_erase_add (s := subsets α s) (f := excess B b X) hmem]
    simp only [excess, ite_true, add_zero, ← sum_sub_distrib]
    apply sum_congr rfl
    intro Y hY
    rw [ite_eq_right (mem_erase.mp hY).1.symm]
  rw [he, hd, off_diagonal_baseline_sum b hX]
  unfold defect
  ring

end CoveringDesigns.MulticoverIncidence
