import CoveringDesigns.C14_5_3.Forty
import CoveringDesigns.C14_5_3.AlmostExactLink

/-! Transport exact and almost-exact point links to actual parent blocks. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem without_point_card (T : Finset α) (x : α) (hx : x ∈ T) :
    (T.subtype (· ∉ ({x} : Finset α))).card = T.card - 1 := by
  rw [card_subtype]
  have he : T.filter (· ∉ ({x} : Finset α)) = T.erase x := by ext p; simp [eq_comm, and_comm]
  rw [he, card_erase_of_mem hx]

theorem insert_without_point (T : Finset α) (x : α) (hx : x ∈ T) :
    ({x} : Finset α) ∪ (T.subtype (· ∉ ({x} : Finset α))).map
      (Function.Embedding.subtype _) = T := by
  ext p
  simp only [mem_union, mem_singleton, mem_map, mem_subtype]
  constructor
  · rintro (rfl | ⟨q,hq,rfl⟩)
    · exact hx
    · exact hq
  · intro hp
    by_cases hpx : p = x
    · exact Or.inl hpx
    · exact Or.inr ⟨⟨p,by simpa using hpx⟩,hp,rfl⟩

theorem link_parent_multiplicity (B : ι → Finset α) (T : Finset α)
    (x : α) (hx : x ∈ T) :
    indexedSubsetDegree (Multicover.subsetLink B {x}) (T.subtype (· ∉ ({x} : Finset α))) =
      indexedSubsetDegree B T := by
  rw [Multicover.subsetLink_multiplicity, insert_without_point T x hx]

theorem without_point_subset_iff (S T : Finset α) (x : α) (hxS : x ∈ S) (hxT : x ∈ T) :
    S.subtype (· ∉ ({x} : Finset α)) ⊆ T.subtype (· ∉ ({x} : Finset α)) ↔ S ⊆ T := by
  constructor
  · intro h p hp
    by_cases hpx : p = x
    · subst p; exact hxT
    · exact mem_subtype.mp (h (x := ⟨p,by simpa using hpx⟩) (mem_subtype.mpr hp))
  · intro h p hp
    exact mem_subtype.mpr (h (mem_subtype.mp hp))

/-- The actual special block is described by both point-pair and point-triple
multiplicities. Its parent occurrence is part of the statement. -/
def SpecialAt (B : ι → Finset α) (x : α) (i : ι) : Prop :=
  x ∈ B i ∧
    (∀ T : Finset α, T.card = 3 → x ∈ T →
      indexedSubsetDegree B T = 1 + if T ⊆ B i then 1 else 0) ∧
    (∀ y : α, y ≠ x →
      indexedSubsetDegree B {x,y} = 4 + if y ∈ B i then 1 else 0)

theorem exists_special {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {x : α} (hx : indexedDegree B x = 14) :
    ∃ i, SpecialAt B x i := by
  classical
  let L := Multicover.subsetLink B {x}
  have hvL : Fintype.card {p : α // p ∉ ({x} : Finset α)} = 13 := by
    rw [Multicover.subset_complement_card,card_singleton,hv]
  have hnL : Fintype.card {i // ({x} : Finset α) ⊆ B i} = 14 := by
    rw [Multicover.subsetLink_card,Multicover.subsetDegree_singleton,hx]
  have hL : Multicover.IsCover L 4 2 1 := by
    simpa [L] using Multicover.subsetLink_isCover hB {x} (by simp)
  obtain ⟨i,hi⟩ := almost_high_block hvL hL hnL
  have hxi : x ∈ B i.val := i.property (mem_singleton_self x)
  refine ⟨i.val,hxi,?_,?_⟩
  · intro T hT hxT
    let U := T.subtype (· ∉ ({x} : Finset α))
    have hU : U.card = 2 := by rw [without_point_card T x hxT,hT]
    have hm := almost_pair_profile hvL hL hnL hU
    rw [←hi] at hm
    have hs : U ⊆ L i ↔ T ⊆ B i.val := without_point_subset_iff T (B i.val) x hxT hxi
    simp only [hs] at hm
    rw [link_parent_multiplicity B T x hxT] at hm
    split_ifs at hm ⊢ <;> omega
  · intro y hyx
    let y' : {p : α // p ∉ ({x} : Finset α)} := ⟨y,by simpa using hyx⟩
    have hs : y' ∈ linkHighPoints L ↔ y ∈ B i.val := by
      rw [←hi]
      exact mem_subtype
    have hm : indexedDegree L y' = indexedSubsetDegree B {x,y} := by
      rw [←Multicover.subsetDegree_singleton,Multicover.subsetLink_multiplicity]
      simp [y']
    by_cases hy : y ∈ B i.val
    · rw [←hm,high_degree_five hvL hL hnL (hs.mpr hy)]
      simp [hy]
    · rw [←hm,low_degree_four hvL hL (fun hh => hy (hs.mp hh))]
      simp [hy]

theorem SpecialAt.duplicate {B : ι → Finset α} {x : α} {i : ι} (h : SpecialAt B x i)
    {T : Finset α} (hT : T.card = 3) (hx : x ∈ T) (hi : T ⊆ B i) :
    indexedSubsetDegree B T = 2 := by simpa [hi] using h.2.1 T hT hx

theorem special_blocks_equal {B : ι → Finset α} (hB : Multicover.Uniform B 5)
    {x y : α} {i j : ι} (hi : SpecialAt B x i) (hj : SpecialAt B y j)
    (hyi : y ∈ B i) : B i = B j := by
  have hsub : B i ⊆ B j := by
    intro z hz
    by_cases hxy : x = y
    · subst y
      by_cases hzx : z = x
      · subst z; exact hj.1
      · have h1 := hi.2.2 z hzx
        have h2 := hj.2.2 z hzx
        simp only [hz,ite_true] at h1
        by_contra hh
        simp only [hh,ite_false] at h2
        omega
    have hxj : x ∈ B j := by
      have h1 := hi.2.2 y (Ne.symm hxy)
      have h2 := hj.2.2 x hxy
      rw [pair_comm y x] at h2
      simp only [hyi,ite_true] at h1
      by_contra hh
      simp only [hh,ite_false] at h2
      omega
    by_cases hzx : z = x
    · subst z; exact hxj
    by_cases hzy : z = y
    · subst z; exact hj.1
    have hT : ({x,y,z} : Finset α).card = 3 := by simp [hxy,Ne.symm hzx,Ne.symm hzy]
    have hTi : ({x,y,z} : Finset α) ⊆ B i := by
      simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨hi.1,hyi,hz⟩
    have h1 := hi.duplicate hT (by simp) hTi
    have h2 := hj.2.1 {x,y,z} hT (by simp)
    have hTj : ({x,y,z} : Finset α) ⊆ B j := by
      by_contra hh
      simp only [hh,ite_false] at h2
      omega
    exact hTj (by simp)
  exact eq_of_subset_of_card_le hsub (by rw [hB i,hB j])

theorem special_avoids_minimum {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {x y : α} {i : ι}
    (hx : indexedDegree B x = 14) (hi : SpecialAt B x i)
    (hy : indexedDegree B y = 13) : y ∉ B i := by
  intro hyi
  have hyx : y ≠ x := by intro he; subst y; omega
  have h1 := hi.2.2 y hyx
  have h2 := minimum_pair_exact hv hB hy (P := {x,y}) (by simp [Ne.symm hyx]) (by simp)
  simp only [hyi,ite_true] at h1
  omega

end CoveringDesigns.C14_5_3
