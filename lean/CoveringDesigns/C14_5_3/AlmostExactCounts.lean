import CoveringDesigns.C14_5_3.Incidence
import Mathlib.Tactic.IntervalCases

/-! Degree and pair excess in fourteen-occurrence pair covers on thirteen points.
The indices are never deduplicated. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

def linkPointExcess (B : ι → Finset α) (x : α) : ℕ := indexedDegree B x - 4
def linkPairExcess (B : ι → Finset α) (x y : α) : ℕ :=
  if x = y then 0 else indexedSubsetDegree B {x,y} - 1
def linkHighPoints (B : ι → Finset α) : Finset α :=
  univ.filter (fun x => 4 < indexedDegree B x)

@[simp] theorem linkPairExcess_self (B : ι → Finset α) (x : α) :
    linkPairExcess B x x = 0 := by simp [linkPairExcess]

theorem linkPairExcess_comm (B : ι → Finset α) (x y : α) :
    linkPairExcess B x y = linkPairExcess B y x := by
  simp [linkPairExcess, eq_comm, pair_comm]

theorem pair_link_point_floor {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (x : α) : 4 ≤ indexedDegree B x := by
  have h := Multicover.multiplicity_ge_of_coverLower hv hB (i := 1) (by omega)
    (Multicover.schoenheim_coverLower (by decide) (by decide)) (X := {x}) (by simp)
  norm_num [Multicover.bound, Schoenheim.ceilDiv, Multicover.subsetDegree_singleton] at h
  exact h

theorem link_excess_sum {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) :
    (∑ x, linkPointExcess B x) = 4 := by
  have hh := sum_congr rfl (fun x (_ : x ∈ (univ : Finset α)) =>
    Nat.sub_add_cancel (pair_link_point_floor hv hB x))
  rw [sum_add_distrib, Multicover.degree_sum_of_uniform hB.1] at hh
  simp only [sum_const, card_univ, Nat.nsmul_eq_mul, hv, hn] at hh
  change (∑ x, linkPointExcess B x) + 13*4 = 4*14 at hh
  omega

theorem link_excess_row {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (x : α) :
    (∑ y, linkPairExcess B x y) = 3 * linkPointExcess B x := by
  classical
  have hh := LabelledCliques.extension_excess_sum hB.1 {x}
    (by simpa using pair_link_point_floor hv hB x)
    (fun P hP => hB.2 P (by have := (LabelledCliques.mem_extensions.mp hP).2; simpa using this))
    (by simp [hv] : (4-({x} : Finset α).card)*4 = (Fintype.card α-({x} : Finset α).card)*1)
  rw [LabelledCliques.sum_extensions] at hh
  simp only [card_singleton, Nat.reduceSub, LabelledCliques.excess,
    Multicover.subsetDegree_singleton] at hh
  have he : (∑ y, linkPairExcess B x y) =
      ∑ y ∈ univ \ ({x} : Finset α), (indexedSubsetDegree B (insert y {x}) - 1) := by
    simp only [linkPairExcess, sum_ite, sum_const_zero, zero_add]
    congr 1
    · ext y
      simp [eq_comm]
    · funext y
      rw [pair_comm]
  rw [he]
  exact hh

theorem link_pair_excess_zero {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) {x : α} (hx : x ∉ linkHighPoints B) (y : α) :
    linkPairExcess B x y = 0 := by
  have hx' : linkPointExcess B x = 0 := by
    simp only [linkHighPoints, mem_filter, mem_univ, true_and, not_lt] at hx
    unfold linkPointExcess
    omega
  have hh := link_excess_row hv hB x
  rw [hx', mul_zero] at hh
  exact (sum_eq_zero_iff.mp hh) y (mem_univ y)

theorem high_excess_sum {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) :
    (∑ x ∈ linkHighPoints B, linkPointExcess B x) = 4 := by
  rw [← link_excess_sum hv hB hn]
  apply sum_subset (subset_univ _)
  intro x _ hx
  simp only [linkHighPoints, mem_filter, mem_univ, true_and, not_lt] at hx
  unfold linkPointExcess
  omega

theorem high_excess_row {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (x : α) :
    (∑ y ∈ linkHighPoints B, linkPairExcess B x y) = 3 * linkPointExcess B x := by
  rw [← link_excess_row hv hB x]
  apply sum_subset (subset_univ _)
  intro y _ hy
  rw [linkPairExcess_comm]
  exact link_pair_excess_zero hv hB hy x

theorem high_excess_pos {B : ι → Finset α} {x : α} (hx : x ∈ linkHighPoints B) :
    1 ≤ linkPointExcess B x := by
  simp only [linkHighPoints, mem_filter, mem_univ, true_and] at hx
  unfold linkPointExcess
  omega

/-- Actual support intersections, rather than a free excess graph, exclude
the three-high-point profile. -/
theorem pair_support_union (B : ι → Finset α) (a b c : α) :
    indexedSubsetDegree B {a,b} + indexedSubsetDegree B {a,c} ≤
      indexedDegree B a + indexedSubsetDegree B {b,c} := by
  classical
  let S := univ.filter (fun i => a ∈ B i ∧ b ∈ B i)
  let T := univ.filter (fun i => a ∈ B i ∧ c ∈ B i)
  have hu : S ∪ T ⊆ univ.filter (fun i => a ∈ B i) := by
    intro i hi
    simp only [S, T, mem_union, mem_filter, mem_univ, true_and] at hi ⊢
    tauto
  have hi : S ∩ T ⊆ univ.filter (fun i => {b,c} ⊆ B i) := by
    intro i hi
    simp only [S, T, mem_inter, mem_filter, mem_univ, true_and,
      insert_subset_iff, singleton_subset_iff] at hi ⊢
    tauto
  have he := card_union_add_card_inter S T
  have hb := add_le_add (card_le_card hu) (card_le_card hi)
  rw [he] at hb
  simpa [S, T, indexedSubsetDegree, indexedDegree, insert_subset_iff, singleton_subset_iff] using hb

theorem high_points_card {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14) :
    (linkHighPoints B).card = 4 := by
  classical
  let H := linkHighPoints B
  have hs := high_excess_sum hv hB hn
  change (∑ x ∈ H, linkPointExcess B x) = 4 at hs
  have hle : H.card ≤ 4 := by
    have h := sum_le_sum (s := H) (fun x hx => high_excess_pos hx)
    simpa [hs] using h
  have hr := high_excess_row hv hB
  have hd (x : α) : linkPointExcess B x + 4 = indexedDegree B x :=
    Nat.sub_add_cancel (pair_link_point_floor hv hB x)
  have hf (x y : α) (hxy : x ≠ y) :
      linkPairExcess B x y + 1 = indexedSubsetDegree B {x,y} := by
    simp only [linkPairExcess, if_neg hxy]
    exact Nat.sub_add_cancel (hB.2 _ (by simp [hxy]))
  have hp (x y : α) : indexedSubsetDegree B {x,y} ≤ indexedDegree B x := by
    simpa only [Multicover.subsetDegree_singleton] using
      multiplicity_mono B (show ({x} : Finset α) ⊆ {x,y} by simp)
  change ∀ x, (∑ y ∈ H, linkPairExcess B x y) = 3 * linkPointExcess B x at hr
  change H.card = 4
  by_contra hne
  have hlt : H.card ≤ 3 := by omega
  interval_cases hc : H.card
  · have hz := card_eq_zero.mp hc
    simp [hz] at hs
  · obtain ⟨a, ha⟩ := card_eq_one.mp hc
    have hra := hr a
    simp [ha] at hs hra
    omega
  · obtain ⟨a, b, hab, he⟩ := card_eq_two.mp hc
    have hra := hr a
    have hrb := hr b
    simp [he, hab, Ne.symm hab, linkPairExcess_comm B b a] at hs hra hrb
    have hab' := hf a b hab
    have hda := hd a
    have hpa := hp a b
    omega
  · obtain ⟨a, b, c, hab, hac, hbc, he⟩ := card_eq_three.mp hc
    have hra := hr a
    have hrb := hr b
    have hrc := hr c
    simp [he, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc,
      linkPairExcess_comm B b a, linkPairExcess_comm B c a, linkPairExcess_comm B c b]
      at hs hra hrb hrc
    have hab' := hf a b hab
    have hac' := hf a c hac
    have hbc' := hf b c hbc
    have hda := hd a
    have hdb := hd b
    have hdc := hd c
    have ha := pair_support_union B a b c
    have hb := pair_support_union B b a c
    have hc := pair_support_union B c a b
    have habsym : indexedSubsetDegree B {b,a} = indexedSubsetDegree B {a,b} := by rw [pair_comm]
    have hacsym : indexedSubsetDegree B {c,a} = indexedSubsetDegree B {a,c} := by rw [pair_comm]
    have hbcsym : indexedSubsetDegree B {c,b} = indexedSubsetDegree B {b,c} := by rw [pair_comm]
    rw [habsym] at hb
    rw [hacsym, hbcsym] at hc
    omega

theorem high_degree_five {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) (hn : Fintype.card ι = 14)
    {x : α} (hx : x ∈ linkHighPoints B) : indexedDegree B x = 5 := by
  have hs := high_excess_sum hv hB hn
  have hc := high_points_card hv hB hn
  have he : (∑ x ∈ linkHighPoints B, 1) = ∑ x ∈ linkHighPoints B, linkPointExcess B x := by
    simp [hs, hc]
  have hh := (sum_eq_sum_iff_of_le (fun x hx => high_excess_pos hx)).mp he x hx
  have hf := pair_link_point_floor hv hB x
  unfold linkPointExcess at hh
  omega

theorem low_degree_four {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) {x : α} (hx : x ∉ linkHighPoints B) :
    indexedDegree B x = 4 := by
  have hf := pair_link_point_floor hv hB x
  simp only [linkHighPoints, mem_filter, mem_univ, true_and, not_lt] at hx
  omega

theorem low_pair_exact {B : ι → Finset α} (hv : Fintype.card α = 13)
    (hB : Multicover.IsCover B 4 2 1) {x y : α} (hxy : x ≠ y)
    (hx : x ∉ linkHighPoints B) : indexedSubsetDegree B {x,y} = 1 := by
  have h := link_pair_excess_zero hv hB hx y
  have hf := hB.2 {x,y} (by simp [hxy])
  simp only [linkPairExcess, if_neg hxy] at h
  omega

end CoveringDesigns.C14_5_3
