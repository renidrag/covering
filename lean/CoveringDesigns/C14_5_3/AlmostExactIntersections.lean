import CoveringDesigns.C14_5_3.AlmostExactTraces
import CoveringDesigns.C14_5_3.ExactLink

/-! Intersections retain actual occurrence indices in the deletion argument. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem almost_small_intersections {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) {i : ι}
    (hi : (B i ∩ linkHighPoints B).card ≤ 1) {j : ι} (hji : j ≠ i) :
    (B j ∩ B i).card ≤ 1 := by
  by_contra hh
  obtain ⟨P,hP,hc⟩ := exists_subset_card_eq (show 2 ≤ (B j ∩ B i).card by omega)
  have hPH : ¬ P ⊆ linkHighPoints B := by
    intro hp
    have hs : P ⊆ B i ∩ linkHighPoints B := subset_inter (hP.trans inter_subset_right) hp
    have := card_le_card hs
    omega
  have hm := multiplicity_ge_two B hji (hP.trans inter_subset_left) (hP.trans inter_subset_right)
  rw [low_pair_exact_of_not_subset hv hB hc hPH] at hm
  omega

theorem almost_intersection_sum {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) (i : ι) :
    (∑ j, (B j ∩ B i).card) = 16 + (B i ∩ linkHighPoints B).card := by
  classical
  have hd (x : α) : indexedDegree B x = 4 + if x ∈ linkHighPoints B then 1 else 0 := by
    by_cases hx : x ∈ linkHighPoints B
    · rw [high_degree_five hv hB hn hx]; simp [hx]
    · rw [low_degree_four hv hB hx]; simp [hx]
  rw [intersection_sum]
  simp_rw [hd]
  rw [sum_add_distrib]
  have he : (∑ x ∈ B i, if x ∈ linkHighPoints B then 1 else 0) =
      (B i ∩ linkHighPoints B).card := by
    rw [← sum_filter, ← card_eq_sum_ones]
    congr 1
  rw [he]
  simp [hB.1 i]

theorem small_intersection_balance (f : ι → ℕ) (i : ι)
    (hn : Fintype.card ι = 14) (hi : f i = 4) (hj : ∀ j, j ≠ i → f j ≤ 1) :
    (univ.filter (fun j => f j = 0)).card + ∑ j, f j = 17 := by
  classical
  have hpoint (j : ι) : f j + (if f j = 0 then 1 else 0) = 1 + if j = i then 3 else 0 := by
    by_cases hji : j = i
    · subst j; simp [hi]
    · have := hj j hji
      split_ifs <;> omega
  have hs := sum_congr rfl (fun j (_ : j ∈ (univ : Finset ι)) => hpoint j)
  have hz : (∑ j : ι, if f j = 0 then 1 else 0) = (univ.filter (fun j => f j = 0)).card := by
    rw [← sum_filter, ← card_eq_sum_ones]
  simp only [sum_add_distrib] at hs
  rw [hz] at hs
  simp only [sum_const, card_univ, Nat.nsmul_eq_mul, mul_one, sum_ite_eq', mem_univ,
    ite_true, hn] at hs
  omega

theorem one_high_meets_all {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) {i : ι}
    (hi : (B i ∩ linkHighPoints B).card = 1) {j : ι} (hji : j ≠ i) :
    (B j ∩ B i).card = 1 := by
  classical
  have hb := small_intersection_balance (fun j => (B j ∩ B i).card) i hn
    (by simp [hB.1 i]) (fun j hj => almost_small_intersections hv hB hi.le hj)
  rw [almost_intersection_sum hv hB hn i, hi] at hb
  have hz : (univ.filter (fun j => (B j ∩ B i).card = 0)) = ∅ := card_eq_zero.mp (by omega)
  have hzero : (B j ∩ B i).card ≠ 0 := by
    intro hzero
    have hm : j ∈ univ.filter (fun j => (B j ∩ B i).card = 0) :=
      mem_filter.mpr ⟨mem_univ j, hzero⟩
    rw [hz] at hm
    exact notMem_empty _ hm
  have := almost_small_intersections hv hB hi.le hji
  omega

theorem low_block_unique_disjoint {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) {i : ι}
    (hi : (B i ∩ linkHighPoints B).card = 0) :
    ∃! j, (B j ∩ B i).card = 0 := by
  classical
  have hb := small_intersection_balance (fun j => (B j ∩ B i).card) i hn
    (by simp [hB.1 i]) (fun j hj => almost_small_intersections hv hB (by omega) hj)
  rw [almost_intersection_sum hv hB hn i, hi] at hb
  have hz : (univ.filter (fun j => (B j ∩ B i).card = 0)).card = 1 := by omega
  obtain ⟨j,hj⟩ := card_eq_one.mp hz
  have he (k : ι) : (B k ∩ B i).card = 0 ↔ k = j := by
    have := congrArg (fun S : Finset ι => k ∈ S) hj
    simpa using this
  exact ⟨j, (he j).mpr rfl, fun k hk => (he k).mp hk⟩

theorem one_high_pair_two {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) {i : ι} {a : α}
    (hi : B i ∩ linkHighPoints B = {a}) {y : α} (hy : y ∈ linkHighPoints B)
    (hya : y ≠ a) : indexedSubsetDegree B {y,a} = 2 := by
  classical
  have ha : a ∈ B i := (mem_inter.mp (hi.symm ▸ mem_singleton_self a)).1
  have hcard : (B i ∩ linkHighPoints B).card = 1 := by rw [hi]; simp
  have hyi : y ∉ B i := by
    intro hyi
    have hh : y ∈ B i ∩ linkHighPoints B := mem_inter.mpr ⟨hyi,hy⟩
    rw [hi] at hh
    exact hya (mem_singleton.mp hh)
  let D := fun j : {j // y ∈ B j} => B j.val
  have hsum : (∑ j, (D j ∩ B i).card) = 5 := by
    have hval (j : {j // y ∈ B j}) : (D j ∩ B i).card = 1 := by
      apply one_high_meets_all hv hB hn hcard
      intro he
      exact hyi (he ▸ j.property)
    rw [sum_const_nat (fun j _ => hval j), card_univ, mul_one]
    change Fintype.card {j // y ∈ B j} = 5
    simpa [Fintype.card_subtype, indexedDegree] using high_degree_five hv hB hn hy
  rw [intersection_sum] at hsum
  have hrest : ∑ z ∈ (B i).erase a, indexedDegree D z = 3 := by
    have hval (z : α) (hz : z ∈ (B i).erase a) : indexedDegree D z = 1 := by
      have hzH : z ∉ linkHighPoints B := by
        intro hzH
        have hh : z ∈ B i ∩ linkHighPoints B := mem_inter.mpr ⟨(mem_erase.mp hz).2,hzH⟩
        rw [hi] at hh
        exact (mem_erase.mp hz).1 (mem_singleton.mp hh)
      have hyz : y ≠ z := by intro he; subst z; exact hyi (mem_erase.mp hz).2
      rw [degree_through_point, pair_comm]
      exact low_pair_exact hv hB (Ne.symm hyz) hzH
    rw [sum_const_nat hval, mul_one, card_erase_of_mem ha, hB.1 i]
  have hsplit := sum_erase_add (B i) (indexedDegree D) ha
  rw [hsum, hrest, degree_through_point] at hsplit
  omega

end CoveringDesigns.C14_5_3
