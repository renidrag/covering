import CoveringDesigns.C14_5_3.MinimumTraces

namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem minimum_pair_trace_sum {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {Z P : Finset α}
    (hZ : ∀ x ∈ Z, indexedDegree B x = 13) (hP : P.card = 2) (hd : Disjoint P Z) :
    (∑ i, if P ⊆ B i then (B i ∩ Z).card else 0) = Z.card := by
  classical
  rw [containing_trace_sum]
  have he (z : α) (hz : z ∈ Z) : indexedSubsetDegree B (insert z P) = 1 := by
    have hzP : z ∉ P := fun hh => disjoint_left.mp hd hh hz
    exact minimum_triple_exact hv hB (hZ z hz) (by simp [hzP,hP]) (by simp)
  rw [sum_congr rfl he]
  simp

/-- The fourth minimum point determines a frame and a distinguished fifth
point. The twelve one-minimum blocks all pass through that point. -/
theorem four_minimum_frame {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {Z : Finset α}
    (hZ : ∀ x ∈ Z, indexedDegree B x = 13) (hz : Z.card = 4) :
    ∃ i p, p ∉ Z ∧ B i = insert p Z ∧
      (∀ j, j ≠ i → (B j ∩ Z).card ≤ 2) ∧
      (univ.filter (fun j => (B j ∩ Z).card = 1)).card = 12 ∧
      (∀ j, (B j ∩ Z).card = 2 → p ∉ B j) ∧
      (∀ j, (B j ∩ Z).card = 1 → p ∈ B j) := by
  classical
  obtain ⟨i,hZi,htrace⟩ := minimum_frame hv hB hZ (by omega)
  have hd : (B i \ Z).card = 1 := by rw [card_sdiff_of_subset hZi,hB.1,hz]
  obtain ⟨p,hp⟩ := card_eq_one.mp hd
  have hpi : p ∈ B i ∧ p ∉ Z := mem_sdiff.mp (by rw [hp]; simp)
  have he : B i = insert p Z := by
    rw [←sdiff_union_of_subset hZi,hp,singleton_union]
  have hti : (B i ∩ Z).card = 4 := by rw [inter_eq_right.mpr hZi,hz]
  have hs := minimum_trace_moments hv hB hZ
  have hc := frame_trace_counts (fun j => (B j ∩ Z).card) i 4 hti (by decide) htrace
  have hn1 : (univ.filter (fun j => (B j ∩ Z).card = 1)).card = 12 := by
    norm_num [hz,Nat.choose] at hs hc
    omega
  have htwo (j : ι) (hj : (B j ∩ Z).card = 2) : p ∉ B j := by
    intro hpj
    let P := B j ∩ Z
    have hpP : p ∉ P := fun h => hpi.2 (mem_inter.mp h).2
    have hT : (insert p P).card = 3 := by simp [hpP,P,hj]
    have hTj : insert p P ⊆ B j := insert_subset hpj inter_subset_left
    have hTi : insert p P ⊆ B i := insert_subset hpi.1 (inter_subset_right.trans hZi)
    obtain ⟨z,hzP⟩ := card_pos.mp (show 0 < P.card by change 0 < (B j ∩ Z).card; omega)
    have hm := minimum_triple_exact hv hB (hZ z (mem_inter.mp hzP).2) hT (mem_insert_of_mem hzP)
    have hji : j ≠ i := by intro hh; subst j; omega
    have := multiplicity_ge_two B hji hTj hTi
    omega
  have hr : (∑ j, if p ∈ B j then (B j ∩ Z).card else 0) = 16 := by
    have hh := containing_trace_sum B {p} Z
    simp only [singleton_subset_iff] at hh
    rw [hh]
    have hm (z : α) (hzZ : z ∈ Z) : indexedSubsetDegree B (insert z {p}) = 4 := by
      have hzp : z ≠ p := by intro hh; subst z; exact hpi.2 hzZ
      exact minimum_pair_exact hv hB (hZ z hzZ) (by simp [hzp]) (by simp)
    rw [sum_congr rfl hm]
    simp [hz]
  have hr' : (univ.filter (fun j => p ∈ B j ∧ (B j ∩ Z).card = 1)).card = 12 := by
    have hterm (j : ι) : (if p ∈ B j then (B j ∩ Z).card else 0) =
        (if j = i then 4 else 0) + (if p ∈ B j ∧ (B j ∩ Z).card = 1 then 1 else 0) := by
      by_cases hji : j = i
      · subst j; simp [hpi.1,hti]
      · have ht := htrace j hji
        have ht2 := htwo j
        interval_cases h : (B j ∩ Z).card <;> simp_all
    rw [sum_congr rfl (fun j _ => hterm j)] at hr
    simp [sum_add_distrib] at hr
    omega
  have hsub : univ.filter (fun j => p ∈ B j ∧ (B j ∩ Z).card = 1) ⊆
      univ.filter (fun j => (B j ∩ Z).card = 1) := by
    intro j hj; simp only [mem_filter,mem_univ,true_and] at *; exact hj.2
  have hf := eq_of_subset_of_card_le hsub (by rw [hr',hn1])
  refine ⟨i,p,hpi.2,he,htrace,hn1,htwo,?_⟩
  intro j hj
  have hm : j ∈ univ.filter (fun j => (B j ∩ Z).card = 1) := by simp [hj]
  rw [←hf] at hm
  exact (mem_filter.mp hm).2.1

end CoveringDesigns.C14_5_3
