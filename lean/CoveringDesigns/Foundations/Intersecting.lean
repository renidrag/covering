import CoveringDesigns.Foundations.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Double counting for indexed families, including repeated members.
The final inequality is the elementary intersecting-triples bound used in
the structural reconstruction of the seven-block (11,5,2) classification.
No classification theorem or finite certificate is used here.
-/

namespace CoveringDesigns

open Finset

/-- The number of occurrences containing a point. The indexing map need not
be injective, so equal sets at different indices remain separate occurrences. -/
def indexedDegree {ι α : Type*} [Fintype ι] [DecidableEq α]
    (S : ι → Finset α) (a : α) : ℕ :=
  (univ.filter fun i => a ∈ S i).card

/-- The number of indexed members containing a given finite subset. -/
def indexedSubsetDegree {ι α : Type*} [Fintype ι] [DecidableEq α]
    (S : ι → Finset α) (T : Finset α) : ℕ :=
  (univ.filter fun i => T ⊆ S i).card

/-- The common points of the members with indices in `I`. An empty `I`
has the whole ambient point set as its common intersection. -/
def indexedCommon {ι α : Type*} [Fintype α] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (I : Finset ι) : Finset α :=
  univ.filter fun a => ∀ i ∈ I, a ∈ S i

@[simp] theorem mem_indexedCommon {ι α : Type*} [Fintype α]
    [DecidableEq ι] [DecidableEq α] (S : ι → Finset α) (I : Finset ι) (a : α) :
    a ∈ indexedCommon S I ↔ ∀ i ∈ I, a ∈ S i := by
  simp [indexedCommon]

@[simp] theorem indexedCommon_pair {ι α : Type*} [Fintype α]
    [DecidableEq ι] [DecidableEq α] (S : ι → Finset α) (i j : ι) :
    indexedCommon S {i, j} = S i ∩ S j := by
  ext a
  simp

/-- Count a point together with `n` distinct indices incident to it, in the
two possible orders. Distinct indices may carry identical sets. -/
theorem sum_choose_filter_card {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : Finset α) (R : ι → α → Prop)
    [∀ i a, Decidable (R i a)] (n : ℕ) :
    (∑ a ∈ t, ((s.filter fun i => R i a).card).choose n) =
      ∑ I ∈ s.powersetCard n, (t.filter fun a => ∀ i ∈ I, R i a).card := by
  have hfilter (a : α) :
      (s.filter fun i => R i a).powersetCard n =
        (s.powersetCard n).filter fun I => ∀ i ∈ I, R i a := by
    ext I
    simp only [mem_powersetCard, mem_filter]
    constructor
    · rintro ⟨hI, hc⟩
      exact ⟨⟨fun i hi => (mem_filter.mp (hI hi)).1, hc⟩,
        fun i hi => (mem_filter.mp (hI hi)).2⟩
    · rintro ⟨⟨hI, hc⟩, hR⟩
      exact ⟨fun i hi => mem_filter.mpr ⟨hI hi, hR i hi⟩, hc⟩
  simp_rw [← card_powersetCard, hfilter]
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]

theorem indexedDegree_choose_sum {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (S : ι → Finset α) (n : ℕ) :
    (∑ a, (indexedDegree S a).choose n) =
      ∑ I ∈ (univ : Finset ι).powersetCard n, (indexedCommon S I).card := by
  exact sum_choose_filter_card univ univ (fun i a => a ∈ S i) n

private theorem pairSubsetFilter {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (r : ℕ) :
    ((univ : Finset α).powersetCard r).filter (fun T => T ⊆ B) =
      B.powersetCard r := by
  ext T
  simp [mem_powersetCard, and_comm]

/-- Count an indexed member together with one of its `r`-element subsets. -/
theorem indexedSubsetDegree_sum {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (S : ι → Finset α) (r : ℕ) :
    (∑ T ∈ (univ : Finset α).powersetCard r, indexedSubsetDegree S T) =
      ∑ i, ((S i).card).choose r := by
  classical
  calc
    _ = ∑ T ∈ (univ : Finset α).powersetCard r,
        ∑ i, if T ⊆ S i then 1 else 0 := by
      simp only [indexedSubsetDegree, card_eq_sum_ones, sum_filter]
    _ = ∑ i, ∑ T ∈ (univ : Finset α).powersetCard r,
        if T ⊆ S i then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter, ← card_eq_sum_ones, pairSubsetFilter, card_powersetCard]

/-- Count an `r`-element point set together with `n` distinct indices of
members containing it. This is the codegree/intersection double count. -/
theorem indexedSubsetDegree_choose_sum {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (S : ι → Finset α) (r n : ℕ) :
    (∑ T ∈ (univ : Finset α).powersetCard r, (indexedSubsetDegree S T).choose n) =
      ∑ I ∈ (univ : Finset ι).powersetCard n, ((indexedCommon S I).card).choose r := by
  unfold indexedSubsetDegree
  rw [sum_choose_filter_card]
  apply sum_congr rfl
  intro I hI
  rw [← card_powersetCard]
  apply congrArg Finset.card
  ext T
  simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨hc, hT⟩
    exact ⟨fun a ha => (mem_indexedCommon S I a).mpr
      (fun i hi => hT i hi ha), hc⟩
  · rintro ⟨hT, hc⟩
    exact ⟨hc, fun i hi a ha => (mem_indexedCommon S I a).mp (hT ha) i hi⟩

private theorem self_le_choose_two_add_one (n : ℕ) : n ≤ n.choose 2 + 1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

/-- An indexed family of pairwise-intersecting triples on seven points.
No injectivity assumption is made on the indexing map. -/
theorem intersecting_triples_bound {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (S : ι → Finset α) (hv : Fintype.card α = 7)
    (hsize : ∀ i, (S i).card = 3)
    (hmeet : ∀ i j, i ≠ j → (S i ∩ S j).Nonempty) :
    (Fintype.card ι).choose 2 + 2 * Fintype.card ι ≤
      (∑ a, (indexedDegree S a).choose 2) + 14 := by
  classical
  let P := (univ : Finset ι).powersetCard 2
  let Q := (univ : Finset α).powersetCard 2
  let qsum := ∑ T ∈ Q, (indexedSubsetDegree S T).choose 2
  have hPcard : P.card = (Fintype.card ι).choose 2 := by
    simp [P]
  have hQcard : Q.card = 21 := by
    simp only [Q, card_powersetCard, card_univ, hv]
    rfl
  have hdegrees : (∑ T ∈ Q, indexedSubsetDegree S T) = 3 * Fintype.card ι := by
    rw [indexedSubsetDegree_sum]
    simp only [hsize]
    change (∑ _ : ι, 3) = 3 * Fintype.card ι
    simp [Nat.mul_comm]
  have hlow : 3 * Fintype.card ι ≤ qsum + 21 := by
    have hh := sum_le_sum (s := Q)
      (fun T _ => self_le_choose_two_add_one (indexedSubsetDegree S T))
    rw [sum_add_distrib] at hh
    simpa [qsum, hdegrees, hQcard] using hh
  have hinter (I : Finset ι) (hI : I ∈ P) :
      2 * ((indexedCommon S I).card).choose 2 + 3 ≤ 3 * (indexedCommon S I).card := by
    have hc : I.card = 2 := mem_powersetCard_univ.mp hI
    obtain ⟨i, j, hne, rfl⟩ := card_eq_two.mp hc
    rw [indexedCommon_pair]
    have hpos := card_pos.mpr (hmeet i j hne)
    have hle : (S i ∩ S j).card ≤ 3 := by
      calc
        _ ≤ (S i).card := card_le_card inter_subset_left
        _ = 3 := hsize i
    have hh : (S i ∩ S j).card = 1 ∨ (S i ∩ S j).card = 2 ∨
        (S i ∩ S j).card = 3 := by omega
    rcases hh with hh | hh | hh <;> rw [hh] <;> decide
  have hqsum : (∑ I ∈ P, ((indexedCommon S I).card).choose 2) = qsum :=
    (indexedSubsetDegree_choose_sum S 2 2).symm
  have hdsum : (∑ I ∈ P, (indexedCommon S I).card) =
      ∑ a, (indexedDegree S a).choose 2 := (indexedDegree_choose_sum S 2).symm
  have hhigh := sum_le_sum (s := P) hinter
  simp only [sum_add_distrib, ← mul_sum] at hhigh
  rw [sum_const_nat (s := P) (m := 3) (fun _ _ => rfl)] at hhigh
  rw [hqsum, hdsum, hPcard] at hhigh
  omega

#print axioms intersecting_triples_bound

end CoveringDesigns
