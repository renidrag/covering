import CoveringDesigns.ProjectiveLinkBounds.Incidence

/-! Füredi (1989) proved the deletion theorem. This follows Sane's elementary
regular/irregular-point proof (1991), with explicit occurrence deletion.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.ProjectiveLinkBounds
open Finset Internal
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

private def highPoints (B : ι → Finset α) (q : ℕ) : Finset α :=
  univ.filter (fun x => q+1 < indexedDegree B x)

private theorem low_degree {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    {x : α} (hx : x ∉ highPoints B q) : indexedDegree B x = q+1 := by
  have hl := pair_point_floor (by omega) hv hB x
  simp only [highPoints, mem_filter, mem_univ, true_and, not_lt] at hx
  omega

private theorem excess_total {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q+1) :
    (∑ x, (indexedDegree B x-(q+1))) = q+1 := by
  have hh := sum_congr rfl (fun x (_ : x ∈ (univ : Finset α)) =>
    Nat.sub_add_cancel (pair_point_floor (by omega) hv hB x))
  rw [sum_add_distrib, Multicover.degree_sum_of_uniform hB.1] at hh
  simp only [sum_const, card_univ, Nat.nsmul_eq_mul, hv, hn] at hh
  nlinarith

private theorem high_excess {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q+1) :
    (∑ x ∈ highPoints B q, (indexedDegree B x-(q+1))) = q+1 := by
  calc
    _ = ∑ x, (indexedDegree B x-(q+1)) := by
      apply sum_subset (subset_univ _)
      intro x _ hx
      rw [low_degree hq hv hB hx, Nat.sub_self]
    _ = q+1 := excess_total hq hv hB hn

private theorem high_card_le {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q+1) : (highPoints B q).card ≤ q+1 := by
  have hs := sum_le_sum (s := highPoints B q) (fun x hx =>
    show 1 ≤ indexedDegree B x-(q+1) from by
      have := (mem_filter.mp hx).2; omega)
  simpa [high_excess hq hv hB hn] using hs

private theorem high_degree {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q+1) (hc : (highPoints B q).card = q+1)
    {x : α} (hx : x ∈ highPoints B q) : indexedDegree B x = q+2 := by
  have hl (y : α) (hy : y ∈ highPoints B q) : 1 ≤ indexedDegree B y-(q+1) := by
    have := (mem_filter.mp hy).2; omega
  have he : (∑ _y ∈ highPoints B q, 1) =
      ∑ y ∈ highPoints B q, (indexedDegree B y-(q+1)) := by
    simp [hc, high_excess hq hv hB hn]
  have hh := (sum_eq_sum_iff_of_le hl).mp he x hx
  omega

private theorem low_pair {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    {x y : α} (hx : x ∉ highPoints B q) (hxy : x ≠ y) :
    indexedSubsetDegree B {x,y} = 1 :=
  regular_pair hv hB (low_degree hq hv hB hx) hxy

private theorem regular_block_exists {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q+1) (hinj : Function.Injective B) :
    ∃ c, ∀ x ∈ B c, x ∉ highPoints B q := by
  classical
  let H := highPoints B q
  have hle : H.card ≤ q+1 := high_card_le hq hv hB hn
  obtain ⟨z,_,hz⟩ := exists_mem_notMem_of_card_lt_card
    (s := H) (t := (univ : Finset α)) (by simp only [card_univ, hv]; unfold pointCount; nlinarith)
  by_contra hno
  have hpos (i : ι) : 1 ≤ (B i ∩ H).card := by
    apply card_pos.mpr
    by_contra hh
    apply hno
    refine ⟨i, fun x hx hxH => hh ⟨x,mem_inter.mpr ⟨hx,hxH⟩⟩⟩
  have hsum (y : α) (hy : y ∉ H) :
      (∑ i : {i // y ∈ B i}, (B i.val ∩ H).card) = H.card := by
    rw [intersection_sum]
    have he (w : α) (hw : w ∈ H) :
        indexedDegree (fun i : {i // y ∈ B i} => B i.val) w = 1 := by
      rw [degree_through_point]
      exact low_pair hq hv hB hy (fun hh => hy (hh ▸ hw))
    rw [sum_const_nat he]; simp
  have hc : H.card = q+1 := by
    have hs := sum_le_sum (s := (univ : Finset {i // z ∈ B i}))
      (fun i _ => hpos i.val)
    rw [hsum z hz] at hs
    have hzc : Fintype.card {i // z ∈ B i} = q+1 := by
      simpa [Fintype.card_subtype, indexedDegree] using low_degree hq hv hB hz
    simp only [sum_const, card_univ, Nat.nsmul_eq_mul, mul_one, hzc] at hs
    omega
  have hone (i : ι) (hi : B i ≠ H) : (B i ∩ H).card = 1 := by
    have hnot : ¬ B i ⊆ H := by
      intro hh
      exact hi (eq_of_subset_of_card_le hh (by rw [hc,hB.1 i]))
    obtain ⟨y,hy,hyH⟩ := not_subset.mp hnot
    have hl (j : {j // y ∈ B j}) (_ : j ∈ univ) : 1 ≤ (B j.val ∩ H).card := hpos j.val
    have he : (∑ _j : {j // y ∈ B j}, 1) =
        ∑ j : {j // y ∈ B j}, (B j.val ∩ H).card := by
      rw [hsum y hyH]
      have hyc : Fintype.card {j // y ∈ B j} = q+1 := by
        simpa [Fintype.card_subtype, indexedDegree] using low_degree hq hv hB hyH
      simp [hyc,hc]
    exact ((sum_eq_sum_iff_of_le hl).mp he ⟨i,hy⟩ (mem_univ _)).symm
  let F := (univ : Finset ι).filter (fun i => B i = H)
  have hfc : F.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    exact hinj ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  have hb (i : ι) : (B i ∩ H).card ≤ 1 + q*(if B i = H then 1 else 0) := by
    by_cases hi : B i = H
    · simp [hi,hc]; omega
    · simp [hi,hone i hi]
  have hs := sum_le_sum (s := (univ : Finset ι)) (fun i _ => hb i)
  have hleft : (∑ i, (B i ∩ H).card) = (q+1)*(q+2) := by
    rw [intersection_sum, sum_const_nat (fun x hx => high_degree hq hv hB hn hc hx), hc]
  have hright : (∑ i : ι, (1+q*(if B i = H then 1 else 0))) = Fintype.card ι + q*F.card := by
    rw [sum_add_distrib, ← mul_sum]
    simp only [sum_const, card_univ, Nat.nsmul_eq_mul, mul_one]
    rw [← sum_filter, ← card_eq_sum_ones]
  rw [hleft,hright,hn] at hs
  unfold pointCount at hs
  nlinarith [Nat.mul_le_mul_left q hfc]

private theorem intersection_le_one {B : ι → Finset α} {c j : ι}
    (hpair : ∀ P ⊆ B c, P.card = 2 → indexedSubsetDegree B P = 1) (hj : j ≠ c) :
    (B j ∩ B c).card ≤ 1 := by
  by_contra hh
  obtain ⟨P,hP,hc⟩ := exists_subset_card_eq (show 2 ≤ (B j ∩ B c).card by omega)
  have hs := multiplicity_ge_two B hj (hP.trans inter_subset_left) (hP.trans inter_subset_right)
  rw [hpair P (hP.trans inter_subset_right) hc] at hs
  omega

private theorem irregular_block {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q+1) (hinj : Function.Injective B) :
    ∃ e, B e = highPoints B q := by
  classical
  obtain ⟨c,hc⟩ := regular_block_exists hq hv hB hn hinj
  have hpair (P : Finset α) (hP : P ⊆ B c) (hp : P.card = 2) :
      indexedSubsetDegree B P = 1 := by
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hp
    exact low_pair hq hv hB (hc x (hP (by simp))) hxy
  have hsum : (∑ i, (B i ∩ B c).card) = (q+1)^2 := by
    rw [intersection_sum, sum_const_nat (fun x hx => low_degree hq hv hB (hc x hx)), hB.1 c]
    ring
  have he : ∃ e, (B e ∩ B c).card = 0 := by
    by_contra hno
    push Not at hno
    have hl := sum_le_sum (s := (univ : Finset ι).erase c)
      (fun i _ => show 1 ≤ (B i ∩ B c).card from by have := hno i; omega)
    have hs := sum_erase_add (univ : Finset ι) (fun i => (B i ∩ B c).card) (mem_univ c)
    simp only [inter_self,hB.1 c,hsum] at hs
    simp only [sum_const,Nat.nsmul_eq_mul,mul_one,card_erase_of_mem (mem_univ c),
      card_univ,hn,Nat.add_sub_cancel] at hl
    unfold pointCount at hl
    nlinarith
  obtain ⟨e,he⟩ := he
  have hsub : B e ⊆ highPoints B q := by
    intro z hz
    by_contra hzH
    have hzc : z ∉ B c := by
      intro hh
      have hz' : z ∈ B e ∩ B c := mem_inter.mpr ⟨hz,hh⟩
      rw [card_eq_zero.mp he] at hz'
      exact notMem_empty _ hz'
    let D := fun i : {i // z ∈ B i} => B i.val
    have hs : (∑ i, (D i ∩ B c).card) = q+1 := by
      rw [intersection_sum]
      have hd (y : α) (hy : y ∈ B c) : indexedDegree D y = 1 := by
        rw [degree_through_point, pair_comm]
        exact low_pair hq hv hB (hc y hy) (fun hh => hzc (hh ▸ hy))
      rw [sum_const_nat hd]; simp [hB.1 c]
    have hl (i : {i // z ∈ B i}) (_ : i ∈ univ) : (D i ∩ B c).card ≤ 1 := by
      apply intersection_le_one hpair
      intro hh
      exact hzc (hh ▸ i.property)
    have hdc : Fintype.card {i // z ∈ B i} = q+1 := by
      simpa [Fintype.card_subtype,indexedDegree] using low_degree hq hv hB hzH
    have hsame : (∑ i, (D i ∩ B c).card) = ∑ _i : {i // z ∈ B i}, 1 := by
      simp [hs,hdc]
    have hh := (sum_eq_sum_iff_of_le hl).mp hsame ⟨e,hz⟩ (mem_univ _)
    change (B e ∩ B c).card = 1 at hh
    omega
  exact ⟨e,eq_of_subset_of_card_le hsub (by rw [hB.1 e]; exact high_card_le hq hv hB hn)⟩

private theorem single_high_block {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q+1) {e : ι} (he : B e = highPoints B q)
    {x : α} (hx : x ∈ highPoints B q) : ∃ c, B c ∩ highPoints B q = {x} := by
  classical
  let H := highPoints B q
  let R := (univ : Finset α) \ H
  have hc : H.card = q+1 := by change (highPoints B q).card = q+1; rw [← he]; exact hB.1 e
  have hxE : x ∈ B e := he.symm ▸ hx
  let D := fun i : {i // x ∈ B i} => B i.val
  let e' : {i // x ∈ B i} := ⟨e,hxE⟩
  have hrc : R.card = q^2 := by
    change ((univ : Finset α) \ H).card = q^2
    rw [card_sdiff_of_subset (subset_univ H),card_univ,hv,hc]
    unfold pointCount
    omega
  have hd : Fintype.card {i // x ∈ B i} = q+2 := by
    simpa [Fintype.card_subtype,indexedDegree] using high_degree hq hv hB hn hc hx
  have hsum : (∑ i, (D i ∩ R).card) = q^2 := by
    rw [intersection_sum]
    have hp (y : α) (hy : y ∈ R) : indexedDegree D y = 1 := by
      have hyH := (mem_sdiff.mp hy).2
      rw [degree_through_point, pair_comm]
      exact low_pair hq hv hB hyH (fun hh => hyH (hh.symm ▸ hx))
    rw [sum_const_nat hp]; simp [hrc]
  by_contra hno
  have hlow (i : {i // x ∈ B i}) (_ : i ∈ (univ : Finset {i // x ∈ B i}).erase e') :
      (D i ∩ R).card ≤ q-1 := by
    have hxI : x ∈ D i ∩ H := mem_inter.mpr ⟨i.property,hx⟩
    have hne : (D i ∩ H).card ≠ 1 := by
      intro hh
      have heq := card_eq_one.mp hh
      obtain ⟨y,hy⟩ := heq
      have hxy : x = y := mem_singleton.mp (hy ▸ hxI)
      exact hno ⟨i.val,by simpa [hxy] using hy⟩
    have hp : 0 < (D i ∩ H).card := card_pos.mpr ⟨x,hxI⟩
    have hs := card_inter_add_card_sdiff (D i) H
    have hr : D i ∩ R = D i \ H := by ext y; simp [R]
    rw [← hr,hB.1 i.val] at hs
    omega
  have hs := sum_le_sum hlow
  have hb := sum_erase_add (univ : Finset {i // x ∈ B i}) (fun i => (D i ∩ R).card) (mem_univ e')
  have hz : (D e' ∩ R).card = 0 := by
    change (B e ∩ R).card = 0
    rw [he]
    simp [R,H]
  rw [hz,add_zero,hsum] at hb
  rw [hb] at hs
  simp only [sum_const,card_erase_of_mem (mem_univ e'),card_univ,hd,
    Nat.nsmul_eq_mul] at hs
  have hq1 : q-1+1=q := by omega
  have hd1 : q+2-1=q+1 := by omega
  rw [hd1] at hs
  nlinarith

private theorem high_pair_two {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q+1) {e : ι} (he : B e = highPoints B q)
    {x y : α} (hx : x ∈ highPoints B q) (hy : y ∈ highPoints B q) (hxy : x ≠ y) :
    indexedSubsetDegree B {x,y} = 2 := by
  classical
  have hH : (highPoints B q).card = q+1 := by rw [← he]; exact hB.1 e
  obtain ⟨c,hc⟩ := single_high_block hq hv hB hn he hx
  have hxc : x ∈ B c := (mem_inter.mp (hc.symm ▸ mem_singleton_self x)).1
  have hlow (z : α) (hz : z ∈ B c) (hzx : z ≠ x) : z ∉ highPoints B q := by
    intro hzH
    have hm : z ∈ B c ∩ highPoints B q := mem_inter.mpr ⟨hz,hzH⟩
    rw [hc] at hm
    exact hzx (mem_singleton.mp hm)
  have hpair (P : Finset α) (hP : P ⊆ B c) (hp : P.card = 2) :
      indexedSubsetDegree B P = 1 := by
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hp
    by_cases ha : a = x
    · rw [pair_comm]
      exact low_pair hq hv hB (hlow b (hP (by simp))
        (fun hh => hab (ha.trans hh.symm))) hab.symm
    · exact low_pair hq hv hB (hlow a (hP (by simp)) ha) hab
  have hsum : (∑ i, (B i ∩ B c).card) = (q+2)+q*(q+1) := by
    rw [intersection_sum]
    have hs := sum_erase_add (B c) (indexedDegree B) hxc
    have hr : (∑ z ∈ (B c).erase x, indexedDegree B z) = q*(q+1) := by
      rw [sum_const_nat (fun z hz => low_degree hq hv hB
        (hlow z (mem_erase.mp hz).2 (mem_erase.mp hz).1)),card_erase_of_mem hxc,hB.1 c]
      congr 1
    rw [hr,high_degree hq hv hB hn hH hx] at hs
    omega
  have hall (i : ι) (hi : i ≠ c) : (B i ∩ B c).card = 1 := by
    have hl (j : ι) (hj : j ∈ (univ : Finset ι).erase c) : (B j ∩ B c).card ≤ 1 :=
      intersection_le_one hpair (mem_erase.mp hj).1
    have hs := sum_erase_add (univ : Finset ι) (fun j => (B j ∩ B c).card) (mem_univ c)
    rw [inter_self,hB.1 c,hsum] at hs
    have hh : (∑ j ∈ (univ : Finset ι).erase c, (B j ∩ B c).card) =
        ∑ _j ∈ (univ : Finset ι).erase c, 1 := by
      simp only [sum_const,Nat.nsmul_eq_mul,mul_one,card_erase_of_mem (mem_univ c),
        card_univ,hn,Nat.add_sub_cancel]
      unfold pointCount
      nlinarith
    exact (sum_eq_sum_iff_of_le hl).mp hh i (by simp [hi])
  have hyc : y ∉ B c := by
    intro hh
    exact hlow y hh hxy.symm hy
  let D := fun i : {i // y ∈ B i} => B i.val
  have hdc : Fintype.card {i // y ∈ B i} = q+2 := by
    simpa [Fintype.card_subtype,indexedDegree] using high_degree hq hv hB hn hH hy
  have hs : (∑ z ∈ B c, indexedSubsetDegree B {y,z}) = q+2 := by
    have hi (i : {i // y ∈ B i}) (_ : i ∈ univ) : (D i ∩ B c).card = 1 := by
      apply hall
      intro hh
      exact hyc (hh ▸ i.property)
    have hcount := intersection_sum D (B c)
    rw [sum_const_nat hi] at hcount
    simpa only [D,degree_through_point,card_univ,hdc,mul_one] using hcount.symm
  have hr : (∑ z ∈ (B c).erase x, indexedSubsetDegree B {y,z}) = q := by
    have hp (z : α) (hz : z ∈ (B c).erase x) : indexedSubsetDegree B {y,z} = 1 := by
      rw [pair_comm]
      exact low_pair hq hv hB (hlow z (mem_erase.mp hz).2 (mem_erase.mp hz).1)
        (fun hh => hyc (hh ▸ (mem_erase.mp hz).2))
    rw [sum_const_nat hp,card_erase_of_mem hxc,hB.1 c]
    omega
  have hh := sum_erase_add (B c) (fun z => indexedSubsetDegree B {y,z}) hxc
  rw [hr,hs,pair_comm y x] at hh
  omega

private theorem delete_balance [DecidableEq ι] (B : ι → Finset α) (i : ι) (T : Finset α) :
    indexedSubsetDegree (fun j : (univ : Finset ι).erase i => B j.val) T +
      (if T ⊆ B i then 1 else 0) = indexedSubsetDegree B T := by
  rw [restrict_multiplicity]
  have he : univ.filter (fun j => j ∈ (univ : Finset ι).erase i ∧ T ⊆ B j) =
      (univ.filter (fun j => T ⊆ B j)).erase i := by
    ext j
    simp [and_comm]
  rw [he]
  by_cases ht : T ⊆ B i
  · have hi : i ∈ univ.filter (fun j => T ⊆ B j) := by simp [ht]
    rw [card_erase_of_mem hi,if_pos ht]
    have hp := card_pos.mpr ⟨i,hi⟩
    unfold indexedSubsetDegree
    omega
  · rw [erase_eq_of_notMem (by simpa using ht),if_neg ht,add_zero]
    rfl

private theorem delete_repaired {B : ι → Finset α} {q : ℕ} (hq : 2 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q+1) (i : ι)
    (hr : ∀ P ⊆ B i, P.card = 2 → 2 ≤ indexedSubsetDegree B P) :
    ∃ J : Finset ι, J.card = pointCount q ∧
      ExactDesign.IsDesign (fun j : J => B j.val) (q+1) 2 1 := by
  classical
  let J := (univ : Finset ι).erase i
  have hj : J.card = pointCount q := by simp [J,card_erase_of_mem,hn]
  refine ⟨J,hj,?_⟩
  apply pair_cover_exact (by omega) hv (hn := by simpa using hj)
  refine ⟨fun j => hB.1 j.val, ?_⟩
  intro P hP
  have hs := delete_balance B i P
  change indexedSubsetDegree (fun j : J => B j.val) P +
    (if P ⊆ B i then 1 else 0) = indexedSubsetDegree B P at hs
  change 1 ≤ indexedSubsetDegree (fun j : J => B j.val) P
  have hl := hB.2 P hP
  by_cases hp : P ⊆ B i
  · have hh := hr P hp hP
    rw [if_pos hp] at hs
    omega
  · rw [if_neg hp] at hs
    omega

/-- Select n surviving input occurrences. Coincident block images are allowed.
The theorem is Füredi's; the elementary proof follows Sane. -/
theorem furedi_sane_deletion {q : ℕ} (hq : 2 ≤ q)
    {B : ι → Finset α} (hv : Fintype.card α = pointCount q)
    (hB : Multicover.IsCover B (q+1) 2 1) (hn : Fintype.card ι = pointCount q+1) :
    ∃ J : Finset ι, J.card = pointCount q ∧
      ExactDesign.IsDesign (fun j : J => B j.val) (q+1) 2 1 := by
  classical
  by_cases hinj : Function.Injective B
  · obtain ⟨e,he⟩ := irregular_block hq hv hB hn hinj
    apply delete_repaired hq hv hB hn e
    intro P hP hp
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hp
    have hx : x ∈ highPoints B q := he ▸ hP (by simp)
    have hy : y ∈ highPoints B q := he ▸ hP (by simp)
    exact (high_pair_two hq hv hB hn he hx hy hxy).ge
  · simp only [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨i,j,hij,hne⟩ := hinj
    apply delete_repaired hq hv hB hn i
    intro P hp _
    exact multiplicity_ge_two B hne hp (hij ▸ hp)

end CoveringDesigns.ProjectiveLinkBounds
