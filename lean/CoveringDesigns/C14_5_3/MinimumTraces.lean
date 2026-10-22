import CoveringDesigns.C14_5_3.SpecialBlocks

/-! Compatibility of several exact point links. Hypotheses concern a chosen
set of degree-thirteen points, without assuming it is the whole minimum set. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

/-- A block missing an exact-link point contains a repeated triple. -/
theorem missed_minimum_triple {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {x : α} (hx : indexedDegree B x = 13)
    (i : ι) (hxi : x ∉ B i) :
    ∃ T : Finset α, T.card = 3 ∧ T ⊆ B i ∧ 2 ≤ indexedSubsetDegree B T := by
  classical
  let L := Multicover.subsetLink B {x}
  let A := residualBlocks B x ⟨i,hxi⟩
  have hvL : Fintype.card {p : α // p ∉ ({x} : Finset α)} = 13 := by
    rw [Multicover.subset_complement_card,card_singleton,hv]
  obtain ⟨T,hT,hm⟩ := no_five_arc hvL (minimum_link_exact hv hB hx) A
    (residual_uniform hB.1 x ⟨i,hxi⟩)
  obtain ⟨j,hj⟩ := (multiplicity_pos_iff L T).mp hm
  let U := T.map (Function.Embedding.subtype _)
  have hUi : U ⊆ B i := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_map.mp hp
    exact mem_subtype.mp ((mem_powersetCard.mp hT).1 hq)
  have hUj : U ⊆ B j.val := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_map.mp hp
    exact mem_subtype.mp (hj hq)
  have hij : i ≠ j.val := by
    intro he
    exact hxi (he ▸ j.property (mem_singleton_self x))
  exact ⟨U,by simpa [U] using (mem_powersetCard.mp hT).2,hUi,
    multiplicity_ge_two B hij hUi hUj⟩

theorem minimum_trace_restriction {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {Z : Finset α}
    (hZ : ∀ x ∈ Z, indexedDegree B x = 13) (i : ι) (hi : ¬ Z ⊆ B i) :
    (B i ∩ Z).card ≤ 2 := by
  classical
  obtain ⟨x,hx,hxi⟩ := Finset.not_subset.mp hi
  obtain ⟨T,ht,hti,hm⟩ := missed_minimum_triple hv hB (hZ x hx) i hxi
  have hd : Disjoint T (B i ∩ Z) := by
    apply disjoint_left.mpr
    intro y hy hy'
    have := minimum_triple_exact hv hB (hZ y (mem_inter.mp hy').2) ht hy
    omega
  have hc := card_le_card (union_subset hti (inter_subset_left : B i ∩ Z ⊆ B i))
  rw [card_union_of_disjoint hd,ht,hB.1] at hc
  omega

theorem minimum_frame {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {Z : Finset α}
    (hZ : ∀ x ∈ Z, indexedDegree B x = 13) (hz : 3 ≤ Z.card) :
    ∃ i, Z ⊆ B i ∧ ∀ j, j ≠ i → (B j ∩ Z).card ≤ 2 := by
  classical
  obtain ⟨T,htZ,ht⟩ := exists_subset_card_eq hz
  obtain ⟨i,hi⟩ := (Multicover.covers_one_iff B 3).mp hB.2 T ht
  have hZi : Z ⊆ B i := by
    by_contra hh
    have hs : T ⊆ B i ∩ Z := subset_inter hi htZ
    have := card_le_card hs
    have := minimum_trace_restriction hv hB hZ i hh
    omega
  refine ⟨i,hZi,?_⟩
  intro j hji
  apply minimum_trace_restriction hv hB hZ
  intro hZj
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < T.card by omega)
  have hm := minimum_triple_exact hv hB (hZ x (htZ hx)) ht hx
  have := multiplicity_ge_two B hji (htZ.trans hZj) hi
  omega

theorem minimum_trace_moments {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {Z : Finset α}
    (hZ : ∀ x ∈ Z, indexedDegree B x = 13) :
    (∑ i, (B i ∩ Z).card) = 13 * Z.card ∧
      (∑ i, ((B i ∩ Z).card).choose 2) = 4 * Z.card.choose 2 := by
  constructor
  · rw [intersection_sum]
    rw [sum_congr rfl hZ]
    simp [Nat.mul_comm]
  · rw [←trace_count]
    have hp (P : Finset α) (hP : P ∈ Z.powersetCard 2) : indexedSubsetDegree B P = 4 := by
      obtain ⟨x,hx⟩ := card_pos.mp (show 0 < P.card by rw [(mem_powersetCard.mp hP).2]; decide)
      exact minimum_pair_exact hv hB (hZ x ((mem_powersetCard.mp hP).1 hx))
        (mem_powersetCard.mp hP).2 hx
    rw [sum_congr rfl hp]
    simp [Nat.mul_comm]

/-- Trace moments with one specified large trace and all other traces at most two. -/
theorem frame_trace_counts [DecidableEq ι] (f : ι → ℕ) (i : ι) (z : ℕ)
    (hi : f i = z) (hz : 3 ≤ z) (hf : ∀ j, j ≠ i → f j ≤ 2) :
    (∑ j, f j) = z + (univ.filter (fun j => f j = 1)).card +
      2 * (univ.filter (fun j => f j = 2)).card ∧
    (∑ j, (f j).choose 2) = z.choose 2 + (univ.filter (fun j => f j = 2)).card := by
  have h1 (j : ι) : f j = (if j = i then z else 0) +
      (if f j = 1 then 1 else 0) + 2 * (if f j = 2 then 1 else 0) := by
    by_cases hj : j = i
    · subst j; simp [hi,show z ≠ 1 by omega,show z ≠ 2 by omega]
    · have := hf j hj
      interval_cases h : f j <;> simp [h,hj]
  have h2 (j : ι) : (f j).choose 2 = (if j = i then z.choose 2 else 0) +
      (if f j = 2 then 1 else 0) := by
    by_cases hj : j = i
    · subst j; simp [hi,show z ≠ 2 by omega]
    · have := hf j hj
      interval_cases h : f j <;> simp [h,hj,Nat.choose]
  constructor
  · rw [sum_congr rfl (fun j _ => h1 j)]
    simp only [sum_add_distrib,←mul_sum]
    simp
  · rw [sum_congr rfl (fun j _ => h2 j)]
    simp [sum_add_distrib]

/-- Sum traces over the actual occurrences containing a fixed subset. -/
theorem containing_trace_sum (B : ι → Finset α) (P Z : Finset α) :
    (∑ i, if P ⊆ B i then (B i ∩ Z).card else 0) =
      ∑ z ∈ Z, indexedSubsetDegree B (insert z P) := by
  classical
  simp only [indexedSubsetDegree,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  by_cases hp : P ⊆ B i
  · simp only [hp,ite_true,insert_subset_iff,true_and,and_true]
    rw [←sum_filter]
    congr 1
    ext x
    simp [and_comm]
  · simp [hp,insert_subset_iff]

end CoveringDesigns.C14_5_3
