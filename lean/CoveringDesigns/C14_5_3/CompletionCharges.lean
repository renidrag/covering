import CoveringDesigns.C14_5_3.Completion

/-! Charging actual noncollinear triples to distinct residual occurrences. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v w
variable {α : Type u} {ι : Type v} {κ : Type w}
  [Fintype α] [DecidableEq α] [Fintype ι] [Fintype κ]

def chargedTriples (L : ι → Finset α) (A M : Finset α) : Finset (Finset α) :=
  (noncollinearTriples L).filter (fun T => T ⊆ A ∧ ¬ Disjoint T M)

/-- The local charge only uses a marked subset of the five-block. It does not
require a classification of five-set collinear-triple counts. -/
theorem block_charge_capacity {L : ι → Finset α} (hv : Fintype.card α = 13)
    (hL : ExactDesign.IsDesign L 4 2 1) {A M : Finset α}
    (hA : A.card = 5) (hM : M ⊆ A) :
    9 ≤ collinearCount L A - 1 + (chargedTriples L A M).card + (5-M.card).choose 3 := by
  let C := (collinearTriples L).filter (· ⊆ A)
  let Q := chargedTriples L A M
  have hs : A.powersetCard 3 ⊆ (C ∪ Q) ∪ (A \ M).powersetCard 3 := by
    intro T ht
    have htc := (mem_powersetCard.mp ht).2
    have htA := (mem_powersetCard.mp ht).1
    by_cases hc : 0 < indexedSubsetDegree L T
    · apply mem_union_left
      apply mem_union_left
      simp [C,collinearTriples,htc,hc,htA]
    · by_cases hd : Disjoint T M
      · apply mem_union_right
        apply mem_powersetCard.mpr
        exact ⟨fun x hx => mem_sdiff.mpr ⟨htA hx,fun hm => disjoint_left.mp hd hx hm⟩,htc⟩
      · apply mem_union_left
        apply mem_union_right
        have hm : indexedSubsetDegree L T = 0 := by omega
        simp [Q,chargedTriples,noncollinearTriples,htc,hm,htA,hd]
  have hcard := card_le_card hs
  have hcu := card_union_le (C ∪ Q) ((A \ M).powersetCard 3)
  have hcu' := card_union_le C Q
  have hc := collinearCount_pos hv hL hA
  rw [card_powersetCard,hA] at hcard
  rw [card_powersetCard,card_sdiff_of_subset hM,hA] at hcu
  change 1 ≤ C.card at hc
  change 9 ≤ C.card - 1 + Q.card + (5-M.card).choose 3
  norm_num only [Nat.choose] at hcard
  omega

theorem block_charge_five {L : ι → Finset α} (hv : Fintype.card α = 13)
    (hL : ExactDesign.IsDesign L 4 2 1) {A M : Finset α}
    (hA : A.card = 5) (hM : M ⊆ A) (hm : M.Nonempty) :
    5 ≤ collinearCount L A - 1 + (chargedTriples L A M).card := by
  have hc := block_charge_capacity hv hL hA hM
  have hp := card_pos.mpr hm
  have hle : (5-M.card).choose 3 ≤ 4 := by
    have hh : 5-M.card ≤ 4 := by omega
    calc
      _ ≤ (4 : ℕ).choose 3 := Nat.choose_le_choose 3 hh
      _ = 4 := by decide
  omega

theorem block_charge_eight {L : ι → Finset α} (hv : Fintype.card α = 13)
    (hL : ExactDesign.IsDesign L 4 2 1) {A M : Finset α}
    (hA : A.card = 5) (hM : M ⊆ A) (hm : M.card = 2) :
    8 ≤ collinearCount L A - 1 + (chargedTriples L A M).card := by
  have hc := block_charge_capacity hv hL hA hM
  norm_num [hm,Nat.choose] at hc
  omega

/-- No numerical defect premise replaces disjointness: the charged triples
must be pairwise disjoint as actual finite sets, and have actual excess. -/
theorem disjoint_charge_budget {L : ι → Finset α} {B : κ → Finset α}
    [DecidableEq κ] (S : Finset κ) (M : κ → Finset α)
    (hd : (S : Set κ).PairwiseDisjoint (fun i => chargedTriples L (B i) (M i)))
    (he : ∀ i ∈ S, ∀ T ∈ chargedTriples L (B i) (M i), 2 ≤ indexedSubsetDegree B T) :
    (∑ i ∈ S, (collinearCount L (B i) - 1 + (chargedTriples L (B i) (M i)).card)) ≤
      completionLoss L B + completionExcess L B := by
  let U := S.biUnion (fun i => chargedTriples L (B i) (M i))
  have hU : U ⊆ noncollinearTriples L := by
    intro T ht
    obtain ⟨i,hi,hT⟩ := mem_biUnion.mp ht
    exact (mem_filter.mp hT).1
  have hE : U.card ≤ completionExcess L B := by
    calc
      U.card = ∑ _T ∈ U, 1 := by simp
      _ ≤ ∑ T ∈ U, (indexedSubsetDegree B T - 1) := by
        apply sum_le_sum
        intro T ht
        obtain ⟨i,hi,hT⟩ := mem_biUnion.mp ht
        have := he i hi T hT
        omega
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hU (by intros; omega)
  have hL : (∑ i ∈ S, (collinearCount L (B i) - 1)) ≤ completionLoss L B :=
    sum_le_sum_of_subset_of_nonneg (subset_univ S) (by intros; omega)
  have hcard : U.card = ∑ i ∈ S, (chargedTriples L (B i) (M i)).card := card_biUnion hd
  rw [sum_add_distrib]
  omega

end CoveringDesigns.C14_5_3
