import CoveringDesigns.C14_5_3.MinimumCompatibility

namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem selected_trace_count [DecidableEq ι] (B : ι → Finset α)
    (S : Finset ι) (R : Finset α) (t : ℕ) :
    (∑ P ∈ R.powersetCard t, (S.filter (fun i => P ⊆ B i)).card) =
      ∑ i ∈ S, ((B i ∩ R).card).choose t := by
  simp only [card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [←sum_filter]
  simp only [←card_eq_sum_ones]
  rw [←card_powersetCard]
  congr 1
  ext P
  simp only [mem_filter,mem_powersetCard,subset_inter_iff]
  tauto

theorem trace_complement_card {B : ι → Finset α} (hB : Multicover.Uniform B 5)
    {Z : Finset α} {p : α} (hp : p ∉ Z) {i : ι} (hpi : p ∈ B i) :
    (B i ∩ (univ \ insert p Z)).card + (B i ∩ Z).card + 1 = 5 := by
  have he : B i ∩ insert p Z = insert p (B i ∩ Z) := by
    ext x
    by_cases hx : x = p
    · subst x; simp [hpi]
    · simp [hx]
  have hr : B i ∩ (univ \ insert p Z) = B i \ insert p Z := by ext x; simp
  rw [hr,card_sdiff,inter_comm (insert p Z) (B i),he,card_insert_of_notMem (by simp [hp]),hB i]
  have hc := card_le_card (inter_subset_left : B i ∩ insert p Z ⊆ B i)
  rw [he,card_insert_of_notMem (by simp [hp]),hB i] at hc
  omega

/-- Retain the actual frame occurrence as well as its high-degree point. -/
private theorem frame_point_sixteen {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {Z : Finset α}
    (hZ : ∀ x ∈ Z, indexedDegree B x = 13) (hz : Z.card = 4) :
    ∃ i p, p ∉ Z ∧ B i = insert p Z ∧ 16 ≤ indexedDegree B p := by
  classical
  obtain ⟨i,p,hp,he,htrace,hn1,htwo,hone⟩ := four_minimum_frame hv hB hZ hz
  let s := fun j => (B j ∩ Z).card
  let S1 := univ.filter (fun j => s j = 1)
  let S2 := univ.filter (fun j => s j = 2)
  let S0 := univ.filter (fun j => p ∈ B j ∧ s j = 0)
  let R := univ \ insert p Z
  have hR : R.card = 9 := by simp [R,card_sdiff_of_subset,hp,hz,hv]
  have hsi : s i = 4 := by simp [s,he,hp,hz]
  have hpframe : p ∈ B i := by simp [he]
  have hrow (P : Finset α) (hP : P ∈ R.powersetCard 2) :
      2 ≤ (S1.filter (fun j => P ⊆ B j)).card + 2 * (S0.filter (fun j => P ⊆ B j)).card := by
    have hPc : P.card = 2 := (mem_powersetCard.mp hP).2
    have hPR : P ⊆ R := (mem_powersetCard.mp hP).1
    have hdis : Disjoint P Z := disjoint_left.mpr (by
      intro z hzP hzZ
      exact (mem_sdiff.mp (hPR hzP)).2 (mem_insert_of_mem hzZ))
    have hpP : p ∉ P := fun h => (mem_sdiff.mp (hPR h)).2 (mem_insert_self _ _)
    have hPi : ¬P ⊆ B i := by
      intro hh
      obtain ⟨q,hq⟩ := card_pos.mp (show 0 < P.card by omega)
      exact (mem_sdiff.mp (hPR hq)).2 (he ▸ hh hq)
    have hr := minimum_pair_trace_sum hv hB hZ hPc hdis
    have hterm (j : ι) : (if P ⊆ B j then s j else 0) =
        (if s j = 1 ∧ P ⊆ B j then 1 else 0) +
          2 * (if s j = 2 ∧ P ⊆ B j then 1 else 0) := by
      by_cases hji : j = i
      · subst j; simp [hPi]
      · have ht := htrace j hji
        change s j ≤ 2 at ht
        interval_cases hh : s j <;> by_cases hj : P ⊆ B j <;> simp [hh,hj]
    change (∑ j, if P ⊆ B j then s j else 0) = Z.card at hr
    rw [sum_congr rfl (fun j _ => hterm j)] at hr
    simp only [sum_add_distrib,←mul_sum] at hr
    have hr' : (S1.filter (fun j => P ⊆ B j)).card +
        2 * (S2.filter (fun j => P ⊆ B j)).card = 4 := by
      simpa [S1,S2,filter_filter,hz] using hr
    have hm := hB.2 (insert p P) (by simp [hpP,hPc])
    have hm' : indexedSubsetDegree B (insert p P) =
        (S1.filter (fun j => P ⊆ B j)).card + (S0.filter (fun j => P ⊆ B j)).card := by
      simp only [indexedSubsetDegree,card_eq_sum_ones,sum_filter,insert_subset_iff,
        S1,S0,mem_filter,mem_univ,true_and]
      rw [←sum_add_distrib]
      apply sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j; simp [hPi]
      · have ht := htrace j hji
        change s j ≤ 2 at ht
        have h1 := hone j
        have h2 := htwo j
        change s j = 1 → p ∈ B j at h1
        change s j = 2 → p ∉ B j at h2
        interval_cases hh : s j <;> by_cases hj : P ⊆ B j <;> simp_all
    rw [hm'] at hm
    omega
  have hs := sum_le_sum (s := R.powersetCard 2) hrow
  have hsum1 : (∑ P ∈ R.powersetCard 2, (S1.filter (fun j => P ⊆ B j)).card) = 36 := by
    rw [selected_trace_count]
    have ht (j : ι) (hj : j ∈ S1) : ((B j ∩ R).card).choose 2 = 3 := by
      have hj1 : s j = 1 := (mem_filter.mp hj).2
      have hc := trace_complement_card hB.1 hp (hone j hj1)
      change (B j ∩ R).card + s j + 1 = 5 at hc
      have hh : (B j ∩ R).card = 3 := by omega
      simp [hh,Nat.choose]
    rw [sum_congr rfl ht]
    have hS1 : S1.card = 12 := hn1
    simp [hS1]
  have hsum0 : (∑ P ∈ R.powersetCard 2, (S0.filter (fun j => P ⊆ B j)).card) = 6 * S0.card := by
    rw [selected_trace_count]
    have ht (j : ι) (hj : j ∈ S0) : ((B j ∩ R).card).choose 2 = 6 := by
      have hj0 : p ∈ B j ∧ s j = 0 := (mem_filter.mp hj).2
      have hc := trace_complement_card hB.1 hp hj0.1
      change (B j ∩ R).card + s j + 1 = 5 at hc
      have hh : (B j ∩ R).card = 4 := by omega
      simp [hh,Nat.choose]
    rw [sum_congr rfl ht]
    simp [Nat.mul_comm]
  rw [sum_add_distrib,←mul_sum,hsum1,hsum0] at hs
  norm_num [hR,Nat.choose] at hs
  have hdegree : indexedDegree B p = 13 + S0.card := by
    have ht (j : ι) : (if p ∈ B j then 1 else 0) =
        (if j = i then 1 else 0) + (if s j = 1 then 1 else 0) +
          (if p ∈ B j ∧ s j = 0 then 1 else 0) := by
      by_cases hji : j = i
      · subst j; simp [hpframe,hsi]
      · have hh := htrace j hji
        change s j ≤ 2 at hh
        have h1 := hone j
        have h2 := htwo j
        change s j = 1 → p ∈ B j at h1
        change s j = 2 → p ∉ B j at h2
        interval_cases hh' : s j <;> simp_all
    unfold indexedDegree
    rw [card_eq_sum_ones,sum_filter,sum_congr rfl (fun j _ => ht j)]
    simp [sum_add_distrib,S0,S1,show S1.card = 12 from hn1]
  refine ⟨i,p,hp,he,?_⟩
  omega


/-- Four chosen degree-thirteen points force a distinct point of degree at
least sixteen. No irredundancy or total-occurrence hypothesis is needed. -/
theorem four_minimum_forces_sixteen {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {Z : Finset α}
    (hZ : ∀ x ∈ Z, indexedDegree B x = 13) (hz : Z.card = 4) :
    ∃ p ∉ Z, 16 ≤ indexedDegree B p := by
  obtain ⟨_,p,hp,_,hd⟩ := frame_point_sixteen hv hB hZ hz
  exact ⟨p,hp,hd⟩

/-- Any chosen five exact-link points are impossible. This also excludes
six or more, without a degree-budget premise. -/
theorem no_five_minimum {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {Z : Finset α}
    (hZ : ∀ x ∈ Z, indexedDegree B x = 13) (hz : Z.card = 5) : False := by
  classical
  obtain ⟨W,hWZ,hw⟩ := exists_subset_card_eq (show 4 ≤ Z.card by omega)
  obtain ⟨i,p,hp,hi,hp16⟩ := frame_point_sixteen hv hB (fun x hx => hZ x (hWZ hx)) hw
  obtain ⟨j,hZj,htrace⟩ := minimum_frame hv hB hZ (by omega)
  have hij : i = j := by
    by_contra hne
    have hle := htrace i hne
    have hsub : W ⊆ B i ∩ Z := subset_inter (hi ▸ subset_insert p W) hWZ
    have hc := card_le_card hsub
    omega
  have he : B j = Z := (eq_of_subset_of_card_le hZj (by rw [hz,hB.1])).symm
  have hpZ : p ∈ Z := by rw [←he,←hij,hi]; simp
  have := hZ p hpZ
  omega

theorem minimum_points_le_four {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {Z : Finset α}
    (hZ : ∀ x ∈ Z, indexedDegree B x = 13) : Z.card ≤ 4 := by
  by_contra hh
  obtain ⟨W,hw,hc⟩ := exists_subset_card_eq (show 5 ≤ Z.card by omega)
  exact no_five_minimum hv hB (fun x hx => hZ x (hw hx)) hc

end CoveringDesigns.C14_5_3
