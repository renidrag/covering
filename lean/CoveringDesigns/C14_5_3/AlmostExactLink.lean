import CoveringDesigns.C14_5_3.AlmostExactIntersections

/-! Deletion of one occurrence from every fourteen-occurrence (13,4,2) cover.
Known antecedent: S. S. Sane, On Affine and Projective Failed Designs (1991).
This is a self-contained special-case proof, not the general theorem. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem four_point_regular (H : Finset α) (hH : H.card = 4) (f : α → α → ℕ)
    (hsym : ∀ x y, f x y = f y x) (hzero : ∀ x, f x x = 0)
    (hrow : ∀ x ∈ H, (∑ y ∈ H, f x y) = 3)
    {a : α} (ha : a ∈ H) (hstar : ∀ y ∈ H, y ≠ a → f a y = 1)
    {x y : α} (hx : x ∈ H) (hy : y ∈ H) (hxy : x ≠ y) : f x y = 1 := by
  by_cases hxa : x = a
  · subst x; exact hstar y hy (Ne.symm hxy)
  by_cases hya : y = a
  · subst y; rw [hsym]; exact hstar x hx hxa
  have hsub : ({a,x,y} : Finset α) ⊆ H := by
    simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨ha,hx,hy⟩
  have hthree : ({a,x,y} : Finset α).card = 3 := by
    simp [Ne.symm hxa, Ne.symm hya, hxy]
  have hc : (H \ {a,x,y}).card = 1 := by rw [card_sdiff_of_subset hsub,hH,hthree]
  obtain ⟨z,hz⟩ := card_eq_one.mp hc
  have hzmem := mem_sdiff.mp (hz.symm ▸ mem_singleton_self z)
  have hza : z ≠ a := by intro he; exact hzmem.2 (by simp [he])
  have hzx : z ≠ x := by intro he; exact hzmem.2 (by simp [he])
  have hzy : z ≠ y := by intro he; exact hzmem.2 (by simp [he])
  have he : H = insert z {a,x,y} := by rw [insert_eq, ←hz, sdiff_union_of_subset hsub]
  have hrx := hrow x hx
  have hry := hrow y hy
  have hrz := hrow z hzmem.1
  have hax := hstar x hx hxa
  have hay := hstar y hy hya
  have haz := hstar z hzmem.1 hza
  simp only [he, sum_insert, mem_insert, mem_singleton, hza, hzx, hzy,
    Ne.symm hxa, Ne.symm hya, hxy, or_self, not_false_eq_true,
    sum_singleton, hzero] at hrx hry hrz
  rw [hsym x a, hax] at hrx
  rw [hsym y a, hay, hsym y x] at hry
  rw [hsym z a, haz, hsym z x, hsym z y] at hrz
  omega

theorem high_pair_excess_one {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14)
    {x y : α} (hx : x ∈ linkHighPoints B) (hy : y ∈ linkHighPoints B) (hxy : x ≠ y) :
    linkPairExcess B x y = 1 := by
  obtain ⟨i,hi⟩ := exists_one_high_block hv hB hn
  obtain ⟨a,ha⟩ := card_eq_one.mp hi
  have haH : a ∈ linkHighPoints B := (mem_inter.mp (ha.symm ▸ mem_singleton_self a)).2
  have hstar (y : α) (hy : y ∈ linkHighPoints B) (hya : y ≠ a) : linkPairExcess B a y = 1 := by
    have hh := one_high_pair_two hv hB hn ha hy hya
    rw [linkPairExcess_comm]
    simp [linkPairExcess, hya, hh]
  apply four_point_regular (linkHighPoints B) (high_points_card hv hB hn)
    (linkPairExcess B) (linkPairExcess_comm B) (linkPairExcess_self B) _ haH hstar hx hy hxy
  intro z hz
  rw [high_excess_row hv hB z]
  simp [linkPointExcess, high_degree_five hv hB hn hz]

/-- The six excess pairs are the actual pairs of the four high points. -/
theorem almost_pair_profile {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14)
    {P : Finset α} (hP : P.card = 2) :
    indexedSubsetDegree B P = if P ⊆ linkHighPoints B then 2 else 1 := by
  classical
  by_cases hp : P ⊆ linkHighPoints B
  · rw [if_pos hp]
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hP
    have he := high_pair_excess_one hv hB hn (hp (by simp)) (hp (by simp)) hxy
    simp only [linkPairExcess, if_neg hxy] at he
    omega
  · rw [if_neg hp]
    exact low_pair_exact_of_not_subset hv hB hP hp

/-- The high four-set occurs as a block; an excess profile alone is insufficient. -/
theorem almost_high_block {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) :
    ∃ j, B j = linkHighPoints B := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨i,hi⟩ := exists_low_block_of_no_high_block hv hB hn hno
  obtain ⟨j,hj,hu⟩ := low_block_unique_disjoint hv hB hn hi
  have hlow (z : α) (hz : z ∈ B i) : z ∉ linkHighPoints B := by
    intro hzH
    have hh : z ∈ B i ∩ linkHighPoints B := mem_inter.mpr ⟨hz,hzH⟩
    rw [card_eq_zero.mp hi] at hh
    exact notMem_empty _ hh
  have hsub : linkHighPoints B ⊆ B j := by
    intro x hx
    have hxi : x ∉ B i := fun hh => hlow x hh hx
    let D := fun k : {k // x ∈ B k} => B k.val
    have hsum : (∑ k, (D k ∩ B i).card) = 4 := by
      rw [intersection_sum]
      have hval (z : α) (hz : z ∈ B i) : indexedDegree D z = 1 := by
        have hzx : z ≠ x := by intro he; subst z; exact hxi hz
        rw [degree_through_point, pair_comm]
        exact low_pair_exact hv hB hzx (hlow z hz)
      rw [sum_const_nat hval, mul_one, hB.1 i]
    have hex : ∃ k : {k // x ∈ B k}, (D k ∩ B i).card = 0 := by
      by_contra hh
      push Not at hh
      have hs := sum_le_sum (s := (univ : Finset {k // x ∈ B k}))
        (fun k _ => show 1 ≤ (D k ∩ B i).card by have := hh k; omega)
      have hc : Fintype.card {k // x ∈ B k} = 5 := by
        simpa [Fintype.card_subtype, indexedDegree] using high_degree_five hv hB hn hx
      simp only [sum_const, card_univ, Nat.nsmul_eq_mul, mul_one, hsum, hc] at hs
      omega
    obtain ⟨k,hk⟩ := hex
    have he := hu k.val hk
    exact he ▸ k.property
  have he : B j = linkHighPoints B := (eq_of_subset_of_card_le hsub
    (by rw [hB.1 j, high_points_card hv hB hn])).symm
  exact hno j he

variable [DecidableEq ι]

/-- Removing one index changes each multiplicity by that index's indicator. -/
theorem delete_index_balance (B : ι → Finset α) (i : ι) (T : Finset α) :
    indexedSubsetDegree (fun j : {j // j ≠ i} => B j.val) T +
      (if T ⊆ B i then 1 else 0) = indexedSubsetDegree B T := by
  classical
  have hs := restrict_add_complement B (fun j => j = i) T
  have he : indexedSubsetDegree (fun j : {j // j = i} => B j.val) T =
      if T ⊆ B i then 1 else 0 := by
    rw [restrict_multiplicity]
    have hf : (univ.filter (fun j => j = i ∧ T ⊆ B j)) = if T ⊆ B i then {i} else ∅ := by
      ext j
      split_ifs <;> simp_all
    rw [hf]
    split_ifs <;> simp
  rw [he] at hs
  simp only [restrict_multiplicity, ne_eq] at hs ⊢
  omega

/-- Delete an occurrence, not all occurrences with its image. Repetition is
allowed in the original covering and no uniqueness of the removed index is asserted. -/
theorem almost_exact_deletion {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) :
    ∃ i, B i = linkHighPoints B ∧
      ExactDesign.IsDesign (fun j : {j // j ≠ i} => B j.val) 4 2 1 := by
  classical
  obtain ⟨i,hi⟩ := almost_high_block hv hB hn
  refine ⟨i,hi,fun j => hB.1 j.val,?_⟩
  intro P hP
  have hb := delete_index_balance B i P
  rw [almost_pair_profile hv hB hn hP, hi] at hb
  split_ifs at hb <;> omega

end CoveringDesigns.C14_5_3
