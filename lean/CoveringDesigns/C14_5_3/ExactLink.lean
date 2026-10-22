import CoveringDesigns.C14_5_3.Incidence
import Mathlib.Tactic.IntervalCases

/-! Consequences of the axioms of an indexed 2-(13,4,1) design.
No coordinate model or uniqueness classification is used. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]
variable {L : ι → Finset α} (hv : Fintype.card α = 13)
    (hL : ExactDesign.IsDesign L 4 2 1)
include hL

include hv in
theorem exact_line_count : Fintype.card ι = 13 := by
  have h := hL.total_count
  norm_num [hv, Nat.choose] at h
  omega

include hv in
theorem exact_point_count (x : α) : indexedDegree L x = 4 := by
  have h := hL.residual_count (i := 1) (by omega) (X := {x}) (by simp)
  norm_num [hv, Multicover.subsetDegree_singleton] at h
  omega

theorem exact_unique_line {P : Finset α} (hP : P.card = 2) :
    ∃! i, P ⊆ L i :=
  (multiplicity_one_iff L P).mp (hL.2 P hP)

theorem exact_line_intersection {i j : ι} (hij : i ≠ j) :
    (L i ∩ L j).card ≤ 1 := by
  by_contra h
  obtain ⟨P, hP, hc⟩ := exists_subset_card_eq (show 2 ≤ (L i ∩ L j).card by omega)
  have hh := multiplicity_ge_two L hij (hP.trans inter_subset_left)
    (hP.trans inter_subset_right)
  rw [hL.2 P hc] at hh
  omega

theorem exact_multiplicity_le_one {T : Finset α} (hT : 2 ≤ T.card) :
    indexedSubsetDegree L T ≤ 1 := by
  obtain ⟨P, hP, hc⟩ := exists_subset_card_eq hT
  exact (multiplicity_mono L hP).trans (hL.2 P hc).le

theorem exact_lines_injective : Function.Injective L := by
  intro i j hij
  by_contra hne
  have h := exact_line_intersection hL hne
  rw [hij, inter_self, hL.1 j] at h
  omega

include hv in
theorem exact_lines_meet (i j : ι) : (L i ∩ L j).Nonempty := by
  classical
  by_cases hij : i = j
  · subst j
    rw [inter_self]
    exact card_pos.mp (by rw [hL.1 i]; omega)
  have hs := intersection_sum L (L i)
  have hsum : (∑ j, (L j ∩ L i).card) = 16 := by
    rw [hs]
    norm_num [exact_point_count hv hL, hL.1 i]
  have ht : ∑ j ∈ univ.erase i, (L j ∩ L i).card = 12 := by
    have := sum_erase_add (univ : Finset ι) (fun j => (L j ∩ L i).card) (mem_univ i)
    simp only [inter_self, hL.1 i, hsum] at this
    omega
  have hb (j : ι) (hj : j ∈ univ.erase i) : (L j ∩ L i).card ≤ 1 :=
    exact_line_intersection hL (mem_erase.mp hj).1
  have he : (∑ j ∈ univ.erase i, (L j ∩ L i).card) =
      ∑ _j ∈ univ.erase i, 1 := by
    rw [ht]
    simp [card_erase_of_mem, exact_line_count hv hL]
  have hj := (sum_eq_sum_iff_of_le hb).mp he j (by simp [Ne.symm hij])
  rw [inter_comm]
  exact card_pos.mp (by omega)

/-- Collinear triples, defined from actual line occurrence multiplicity. -/
def collinearTriples (L : ι → Finset α) : Finset (Finset α) :=
  (univ.powersetCard 3).filter (fun T => 0 < indexedSubsetDegree L T)

def noncollinearTriples (L : ι → Finset α) : Finset (Finset α) :=
  (univ.powersetCard 3).filter (fun T => indexedSubsetDegree L T = 0)

include hv in
theorem collinear_card : (collinearTriples L).card = 52 := by
  have hs := Multicover.subsetDegree_sum_of_uniform hL.1 3
  have he : (∑ T ∈ (univ : Finset α).powersetCard 3, indexedSubsetDegree L T) =
      (collinearTriples L).card := by
    rw [collinearTriples, card_eq_sum_ones, sum_filter]
    apply sum_congr rfl
    intro T hT
    have hm := exact_multiplicity_le_one hL (T := T)
      (by have := (mem_powersetCard.mp hT).2; omega)
    split_ifs <;> omega
  rw [he, exact_line_count hv hL] at hs
  norm_num at hs
  exact hs

include hv in
theorem noncollinear_card : (noncollinearTriples L).card = 234 := by
  have h := card_filter_add_card_filter_not
    (s := (univ : Finset α).powersetCard 3) (fun T => 0 < indexedSubsetDegree L T)
  have he : ((univ : Finset α).powersetCard 3).filter
      (fun T => ¬ 0 < indexedSubsetDegree L T) = noncollinearTriples L := by
    ext T
    simp [noncollinearTriples]
  rw [he, ← collinearTriples, collinear_card hv hL, card_powersetCard, card_univ, hv] at h
  norm_num [Nat.choose] at h
  omega

omit hL in
theorem degree_through_point (B : ι → Finset α) (p q : α) :
    indexedDegree (fun i : {i // p ∈ B i} => B i) q = indexedSubsetDegree B {p, q} := by
  classical
  rw [← Multicover.subsetDegree_singleton, restrict_multiplicity]
  unfold indexedSubsetDegree
  congr 1
  ext i
  simp [insert_subset_iff, singleton_subset_iff]

include hv in
/-- The elementary parity proof: every five-set contains a collinear triple. -/
theorem no_five_arc (A : Finset α) (hA : A.card = 5) :
    ∃ T ∈ A.powersetCard 3, 0 < indexedSubsetDegree L T := by
  classical
  by_contra hn
  push_neg at hn
  have htrace (i : ι) : (L i ∩ A).card ≤ 2 := by
    by_contra hh
    obtain ⟨T, hT, hc⟩ := exists_subset_card_eq (show 3 ≤ (L i ∩ A).card by omega)
    have hz := hn T (mem_powersetCard.mpr ⟨hT.trans inter_subset_right, hc⟩)
    have hp := (multiplicity_pos_iff L T).mpr ⟨i, hT.trans inter_subset_left⟩
    omega
  have hpair : (∑ i, ((L i ∩ A).card).choose 2) = 10 := by
    rw [← trace_count]
    have he := sum_congr rfl (fun P (hP : P ∈ A.powersetCard 2) =>
      hL.2 P (mem_powersetCard.mp hP).2)
    rw [he]
    norm_num [hA, Nat.choose]
  have hpoint : (∑ i, (L i ∩ A).card) = 20 := by
    rw [intersection_sum]
    norm_num [exact_point_count hv hL, hA]
  have hle (i : ι) (_ : i ∈ (univ : Finset ι)) :
      2 * ((L i ∩ A).card).choose 2 ≤ (L i ∩ A).card := by
    have := htrace i
    interval_cases h : (L i ∩ A).card <;> norm_num
  have he : (∑ i, 2 * ((L i ∩ A).card).choose 2) = ∑ i, (L i ∩ A).card := by
    rw [← mul_sum, hpair, hpoint]
    norm_num
  have heach := (sum_eq_sum_iff_of_le hle).mp he
  have heven (i : ι) : 2 ∣ (L i ∩ A).card := by
    rw [← heach i (mem_univ i)]
    exact dvd_mul_right _ _
  obtain ⟨z, hz, hzA⟩ := exists_mem_notMem_of_card_lt_card
    (s := A) (t := univ) (by simp [hv, hA])
  let M := fun i : {i // z ∈ L i} => L i
  have hm : (∑ i, (M i ∩ A).card) = 5 := by
    rw [intersection_sum]
    have hmq (q : α) (hq : q ∈ A) : indexedDegree M q = 1 := by
      have hne : z ≠ q := by intro he; subst q; exact hzA hq
      rw [degree_through_point]
      exact hL.2 _ (by simp [hne])
    rw [sum_congr rfl hmq]
    simp [hA]
  have hd : 2 ∣ ∑ i, (M i ∩ A).card :=
    dvd_sum (fun i _ => heven i.val)
  rw [hm] at hd
  norm_num at hd

end CoveringDesigns.C14_5_3
