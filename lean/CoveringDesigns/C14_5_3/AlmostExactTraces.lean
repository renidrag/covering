import CoveringDesigns.C14_5_3.AlmostExactCounts

/-! Actual block traces in an almost-exact link. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem subset_filter_powerset (S : Finset α) (r : ℕ) :
    ((univ : Finset α).powersetCard r).filter (· ⊆ S) = S.powersetCard r := by
  ext T
  simp [mem_powersetCard, and_comm]

theorem low_pair_exact_of_not_subset {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) {P : Finset α} (hP : P.card = 2)
    (hPH : ¬ P ⊆ linkHighPoints B) : indexedSubsetDegree B P = 1 := by
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hP
  by_cases ha : a ∈ linkHighPoints B
  · have hb : b ∉ linkHighPoints B := by
      intro hb
      exact hPH (by simp [insert_subset_iff, singleton_subset_iff, ha,hb])
    rw [pair_comm]
    exact low_pair_exact hv hB (Ne.symm hab) hb
  · exact low_pair_exact hv hB hab ha

theorem high_pair_sum {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) :
    (∑ P ∈ (linkHighPoints B).powersetCard 2, indexedSubsetDegree B P) = 12 := by
  classical
  let H := linkHighPoints B
  have hc : H.card = 4 := high_points_card hv hB hn
  have hs := sum_filter_add_sum_filter_not ((univ : Finset α).powersetCard 2)
    (fun P => P ⊆ H) (indexedSubsetDegree B)
  have hd := card_filter_add_card_filter_not (s := (univ : Finset α).powersetCard 2)
    (fun P => P ⊆ H)
  rw [subset_filter_powerset, Multicover.subsetDegree_sum_of_uniform hB.1] at hs
  rw [subset_filter_powerset, card_powersetCard, hc, card_powersetCard, card_univ, hv] at hd
  have he : (∑ P ∈ ((univ : Finset α).powersetCard 2).filter (fun P => ¬ P ⊆ H),
      indexedSubsetDegree B P) =
      (((univ : Finset α).powersetCard 2).filter (fun P => ¬ P ⊆ H)).card := by
    rw [sum_const_nat (m := 1)]
    · simp
    · intro P hP
      have hp := mem_filter.mp hP
      exact low_pair_exact_of_not_subset hv hB (mem_powersetCard.mp hp.1).2 hp.2
  rw [he, hn] at hs
  norm_num [Nat.choose] at hd hs
  change (∑ P ∈ H.powersetCard 2, indexedSubsetDegree B P) = 12
  omega

def traceCount (B : ι → Finset α) (H : Finset α) (s : ℕ) : ℕ :=
  (univ.filter (fun i => (B i ∩ H).card = s)).card

theorem bounded_fiber_sum (r : ι → ℕ) (n : ℕ) (hr : ∀ i, r i ≤ n) (f : ℕ → ℕ) :
    (∑ i, f (r i)) = ∑ j ∈ range (n+1), (univ.filter (fun i => r i = j)).card * f j := by
  classical
  have hm (i : ι) (_ : i ∈ (univ : Finset ι)) : r i ∈ range (n+1) := mem_range.mpr (by have := hr i; omega)
  rw [← sum_fiberwise_of_maps_to hm (fun i => f (r i))]
  apply sum_congr rfl
  intro j hj
  exact sum_const_nat (fun i hi => congrArg f (mem_filter.mp hi).2)

theorem high_trace_moments {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) :
    let n := traceCount B (linkHighPoints B)
    n 0+n 1+n 2+n 3+n 4 = 14 ∧
      n 1+2*n 2+3*n 3+4*n 4 = 20 ∧ n 2+3*n 3+6*n 4 = 12 := by
  classical
  let H := linkHighPoints B
  have hc : H.card = 4 := high_points_card hv hB hn
  have hr (i : ι) : (B i ∩ H).card ≤ 4 := (card_le_card inter_subset_left).trans_eq (hB.1 i)
  have h0 := bounded_fiber_sum (fun i => (B i ∩ H).card) 4 hr (fun _ => 1)
  have h1 := bounded_fiber_sum (fun i => (B i ∩ H).card) 4 hr id
  have h2 := bounded_fiber_sum (fun i => (B i ∩ H).card) 4 hr (fun s => s.choose 2)
  have ht : (∑ i, (B i ∩ H).card) = 20 := by
    rw [intersection_sum]
    rw [sum_const_nat (fun x hx => high_degree_five hv hB hn hx), hc]
  have hp : (∑ i, ((B i ∩ H).card).choose 2) = 12 := by
    rw [← trace_count]
    exact high_pair_sum hv hB hn
  simp only [sum_const, card_univ, Nat.nsmul_eq_mul, mul_one, hn] at h0
  simp only [id_eq] at h1
  rw [ht] at h1
  rw [hp] at h2
  norm_num [sum_range_succ, Nat.choose, Nat.mul_comm] at h0 h1 h2
  dsimp only [H] at h0 h1 h2
  dsimp only [traceCount]
  exact ⟨by simpa only [card_eq_zero] using h0.symm, h1.symm, h2.symm⟩

theorem exists_one_high_block {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) :
    ∃ i, (B i ∩ linkHighPoints B).card = 1 := by
  have hm := high_trace_moments hv hB hn
  dsimp only at hm
  have hp : 0 < traceCount B (linkHighPoints B) 1 := by omega
  obtain ⟨i, hi⟩ := card_pos.mp hp
  exact ⟨i, (mem_filter.mp hi).2⟩

theorem exists_low_block_of_no_high_block {B : ι → Finset α}
    (hv : Fintype.card α = 13) (hB : Multicover.IsCover B 4 2 1)
    (hn : Fintype.card ι = 14) (hno : ∀ i, B i ≠ linkHighPoints B) :
    ∃ i, (B i ∩ linkHighPoints B).card = 0 := by
  classical
  have hz : traceCount B (linkHighPoints B) 4 = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hc := (mem_filter.mp hi).2
    have hleft := eq_of_subset_of_card_le inter_subset_left (by rw [hB.1 i, hc])
    have hright := eq_of_subset_of_card_le inter_subset_right (by rw [high_points_card hv hB hn, hc])
    exact hno i (hleft.symm.trans hright)
  have hm := high_trace_moments hv hB hn
  dsimp only at hm
  have hp : 0 < traceCount B (linkHighPoints B) 0 := by omega
  obtain ⟨i, hi⟩ := card_pos.mp hp
  exact ⟨i, (mem_filter.mp hi).2⟩

end CoveringDesigns.C14_5_3
