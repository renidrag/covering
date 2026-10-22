import CoveringDesigns.C14_5_3.ParentLinks

/-! Special blocks, their actual occurrence groups, and private triples. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

noncomputable def specialIndices (B : ι → Finset α) : Finset ι :=
  by classical exact univ.filter (fun i => ∃ x, indexedDegree B x = 14 ∧ SpecialAt B x i)

noncomputable def middlePoints (B : ι → Finset α) : Finset α :=
  univ.filter (fun x => indexedDegree B x = 14)

noncomputable def highPoints (B : ι → Finset α) : Finset α :=
  univ.filter (fun x => 15 ≤ indexedDegree B x)

theorem mem_specialIndices {B : ι → Finset α} {i : ι} :
    i ∈ specialIndices B ↔ ∃ x, indexedDegree B x = 14 ∧ SpecialAt B x i := by
  classical simp [specialIndices]

theorem special_at_member {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hirr : Irredundant B 3)
    {i : ι} (hi : i ∈ specialIndices B) {y : α}
    (hy : indexedDegree B y = 14) (hyi : y ∈ B i) : SpecialAt B y i := by
  obtain ⟨x,hx,hxi⟩ := mem_specialIndices.mp hi
  obtain ⟨j,hj⟩ := exists_special hv hB hy
  have he : i = j := hirr.injective (special_blocks_equal hB.1 hxi hj hyi)
  simpa [he] using hj

theorem special_group_unique {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hirr : Irredundant B 3)
    {i j : ι} (hi : i ∈ specialIndices B) (hj : j ∈ specialIndices B)
    {y : α} (hy : indexedDegree B y = 14) (hyi : y ∈ B i) (hyj : y ∈ B j) : i = j := by
  have h1 := special_at_member hv hB hirr hi hy hyi
  have h2 := special_at_member hv hB hirr hj hy hyj
  exact hirr.injective (special_blocks_equal hB.1 h1 h2 hyi)

theorem private_high {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hirr : Irredundant B 3)
    {i : ι} (hi : i ∈ specialIndices B) {T : Finset α}
    (ht : T.card = 3) (hti : T ⊆ B i) (hm : indexedSubsetDegree B T = 1) :
    T ⊆ highPoints B := by
  classical
  obtain ⟨x,hx,hxi⟩ := mem_specialIndices.mp hi
  intro y hy
  have hf := point_floor hv hB y
  have h13 : indexedDegree B y ≠ 13 := by
    intro he
    exact special_avoids_minimum hv hB hx hxi he (hti hy)
  have h14 : indexedDegree B y ≠ 14 := by
    intro he
    have hh := (special_at_member hv hB hirr hi he (hti hy)).duplicate ht hy hti
    omega
  simp only [highPoints, mem_filter, mem_univ, true_and]
  omega

theorem special_middle_le_two {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hirr : Irredundant B 3)
    {i : ι} (hi : i ∈ specialIndices B) : (B i ∩ middlePoints B).card ≤ 2 := by
  classical
  obtain ⟨T,ht,hti,hm⟩ := hirr.private_multiplicity i
  have hh := private_high hv hB hirr hi ht hti hm
  have hd : Disjoint T (B i ∩ middlePoints B) := by
    apply disjoint_left.mpr
    intro x hx hx'
    have h1 := mem_filter.mp (hh hx)
    have h2 := mem_filter.mp (mem_inter.mp hx').2
    omega
  have hs : T ∪ (B i ∩ middlePoints B) ⊆ B i := union_subset hti inter_subset_left
  have hc := card_le_card hs
  rw [card_union_of_disjoint hd,ht,hB.1] at hc
  omega

/-- Double counting restricted to an explicit set of occurrence identities. -/
theorem selected_intersection_sum [DecidableEq ι] (B : ι → Finset α)
    (S : Finset ι) (H : Finset α) :
    (∑ i ∈ S, (B i ∩ H).card) = ∑ x ∈ H, (S.filter (fun i => x ∈ B i)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [←sum_filter]
  congr 1
  ext x
  simp [and_comm]

theorem special_group_count {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hirr : Irredundant B 3) :
    (∑ i ∈ specialIndices B, (B i ∩ middlePoints B).card) = (middlePoints B).card := by
  classical
  rw [selected_intersection_sum]
  rw [←Nat.mul_one (middlePoints B).card]
  apply sum_const_nat (m := 1)
  intro x hx
  have hdx : indexedDegree B x = 14 := (mem_filter.mp hx).2
  obtain ⟨i,hi⟩ := exists_special hv hB hdx
  apply card_eq_one.mpr
  refine ⟨i, ?_⟩
  ext j
  simp only [mem_filter,mem_singleton]
  constructor
  · intro hj
    exact special_group_unique hv hB hirr hj.1 (mem_specialIndices.mpr ⟨x,hdx,hi⟩) hdx hj.2 hi.1
  · rintro rfl
    exact ⟨mem_specialIndices.mpr ⟨x,hdx,hi⟩,hi.1⟩

theorem middle_le_twice_special {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hirr : Irredundant B 3) :
    (middlePoints B).card ≤ 2 * (specialIndices B).card := by
  rw [←special_group_count hv hB hirr]
  calc
    _ ≤ ∑ _i ∈ specialIndices B, 2 := sum_le_sum (fun i hi => special_middle_le_two hv hB hirr hi)
    _ = _ := by simp [Nat.mul_comm]

theorem distinct_private_triples {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hirr : Irredundant B 3) :
    (specialIndices B).card ≤ ((highPoints B).card).choose 3 := by
  classical
  have hp := hirr
  choose T ht hti hu using hp
  have hmem (i : ι) (hi : i ∈ specialIndices B) : T i ∈ (highPoints B).powersetCard 3 := by
    apply mem_powersetCard.mpr
    exact ⟨private_high hv hB hirr hi (ht i) (hti i)
      ((multiplicity_one_iff B (T i)).mpr ⟨i,hti i,hu i⟩),ht i⟩
  have hinj : Set.InjOn T (specialIndices B) := by
    intro i hi j hj he
    exact (hu i j (he ▸ hti j)).symm
  rw [←card_powersetCard]
  exact card_le_card_of_injOn T hmem hinj

end CoveringDesigns.C14_5_3
