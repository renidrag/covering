import CoveringDesigns.C14_5_3.SpecialBlocks
import CoveringDesigns.C14_5_3.CompletionCharges

namespace CoveringDesigns.C14_5_3
open Finset
universe u v w
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem subtype_map_subset {p : α → Prop} [DecidablePred p]
    (T : Finset {x // p x}) (A : Finset α) :
    T.map (Function.Embedding.subtype p) ⊆ A ↔ T ⊆ A.subtype p := by
  constructor
  · intro h x hx
    exact mem_subtype.mpr (h (mem_map.mpr ⟨x,hx,rfl⟩))
  · intro h x hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    exact mem_subtype.mp (h hy)

theorem subtype_values_multiplicity {p : α → Prop} [DecidablePred p]
    (B : ι → Finset α) (T : Finset {x // p x}) :
    indexedSubsetDegree (fun i => (B i).subtype p) T =
      indexedSubsetDegree B (T.map (Function.Embedding.subtype p)) := by
  unfold indexedSubsetDegree
  congr 1
  ext i
  simp [subtype_map_subset]

theorem residual_multiplicity_split (B : ι → Finset α) (x : α)
    (T : Finset {p : α // p ∉ ({x} : Finset α)}) :
    indexedSubsetDegree (Multicover.subsetLink B {x}) T +
      indexedSubsetDegree (residualBlocks B x) T =
        indexedSubsetDegree B (T.map (Function.Embedding.subtype _)) := by
  classical
  change indexedSubsetDegree (fun i : {i // ({x}:Finset α) ⊆ B i} =>
      (B i.val).subtype (· ∉ ({x}:Finset α))) T +
    indexedSubsetDegree (fun i : {i // x ∉ B i} =>
      (B i.val).subtype (· ∉ ({x}:Finset α))) T = _
  rw [subtype_values_multiplicity,subtype_values_multiplicity]
  simpa only [restrict_multiplicity, singleton_subset_iff] using
    restrict_add_complement B (fun i => x ∈ B i) (T.map (Function.Embedding.subtype _))

noncomputable def residualSpecials (B : ι → Finset α) (x : α) : Finset {i // x ∉ B i} :=
  by classical exact univ.filter (fun i => i.val ∈ specialIndices B)

noncomputable def residualMarks (B : ι → Finset α) (x : α) (i : {i // x ∉ B i}) :
    Finset {p : α // p ∉ ({x} : Finset α)} :=
  (residualBlocks B x i).filter (fun p => indexedDegree B p.val = 14)

theorem residual_specials_card {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {x : α} (hx : indexedDegree B x = 13) :
    (residualSpecials B x).card = (specialIndices B).card := by
  classical
  have he : residualSpecials B x = (specialIndices B).subtype (fun i => x ∉ B i) := by
    ext i; simp [residualSpecials]
  rw [he,card_subtype]
  congr 1
  apply filter_eq_self.mpr
  intro i hi
  obtain ⟨y,hy,hyi⟩ := mem_specialIndices.mp hi
  exact special_avoids_minimum hv hB hy hyi hx

theorem residual_marks_nonempty {B : ι → Finset α} {x : α}
    {i : {i // x ∉ B i}} (hi : i ∈ residualSpecials B x) :
    (residualMarks B x i).Nonempty := by
  classical
  obtain ⟨y,hy,hyi⟩ := mem_specialIndices.mp (mem_filter.mp hi).2
  have hyx : y ≠ x := by intro he; subst y; exact i.property hyi.1
  exact ⟨⟨y,by simpa using hyx⟩,mem_filter.mpr ⟨mem_subtype.mpr hyi.1,hy⟩⟩

theorem residual_charges_disjoint {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hirr : Irredundant B 3) (x : α) :
    ((residualSpecials B x) : Set {i // x ∉ B i}).PairwiseDisjoint
      (fun i => chargedTriples (Multicover.subsetLink B {x}) (residualBlocks B x i) (residualMarks B x i)) := by
  classical
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro T hTi hTj
  have hm := (mem_filter.mp hTi).2
  have hmj := (mem_filter.mp hTj).2
  obtain ⟨y,hyT,hyM⟩ := not_disjoint_iff.mp hm.2
  have hyd : indexedDegree B y.val = 14 := (mem_filter.mp hyM).2
  have hyi : y.val ∈ B i.val := mem_subtype.mp (hm.1 hyT)
  have hyj : y.val ∈ B j.val := mem_subtype.mp (hmj.1 hyT)
  have he := special_group_unique hv hB hirr (mem_filter.mp hi).2 (mem_filter.mp hj).2 hyd hyi hyj
  exact hij (Subtype.ext he)

theorem residual_charge_excess {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hirr : Irredundant B 3) (x : α)
    {i : {i // x ∉ B i}} (hi : i ∈ residualSpecials B x)
    {T : Finset {p : α // p ∉ ({x} : Finset α)}}
    (hT : T ∈ chargedTriples (Multicover.subsetLink B {x}) (residualBlocks B x i) (residualMarks B x i)) :
    indexedSubsetDegree (residualBlocks B x) T = 2 := by
  classical
  have ht := (mem_filter.mp hT).1
  have htcard := (mem_powersetCard.mp (mem_filter.mp ht).1).2
  have htzero := (mem_filter.mp ht).2
  have hm := (mem_filter.mp hT).2
  obtain ⟨y,hyT,hyM⟩ := not_disjoint_iff.mp hm.2
  have hyd : indexedDegree B y.val = 14 := (mem_filter.mp hyM).2
  have hs := special_at_member hv hB hirr (mem_filter.mp hi).2 hyd (mem_subtype.mp (hm.1 hyT))
  have hdup := hs.duplicate (T := T.map (Function.Embedding.subtype _))
    (by simpa using htcard) (mem_map.mpr ⟨y,hyT,rfl⟩) ((subtype_map_subset T (B i.val)).mpr hm.1)
  have hsplit := residual_multiplicity_split B x T
  omega

theorem residual_marks_card (B : ι → Finset α) (x : α) (i : {i // x ∉ B i}) :
    (residualMarks B x i).card = (B i.val ∩ middlePoints B).card := by
  classical
  have he : residualMarks B x i = (B i.val ∩ middlePoints B).subtype (· ∉ ({x}:Finset α)) := by
    ext p
    simp [residualMarks,residualBlocks,middlePoints]
  rw [he,card_subtype]
  congr 1
  apply filter_eq_self.mpr
  intro p hp
  simp only [mem_singleton]
  intro hpx
  subst p
  exact i.property (mem_inter.mp hp).1

/-- The eight-unit charge retains the actual two middle points of its block. -/
theorem special_charge_eight {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {x : α} (hx : indexedDegree B x = 13)
    (i : {i // x ∉ B i}) (hm : (B i.val ∩ middlePoints B).card = 2) :
    8 ≤ collinearCount (Multicover.subsetLink B {x}) (residualBlocks B x i) - 1 +
      (chargedTriples (Multicover.subsetLink B {x}) (residualBlocks B x i) (residualMarks B x i)).card := by
  apply block_charge_eight (by rw [Multicover.subset_complement_card,card_singleton,hv])
    (minimum_link_exact hv hB hx) (residual_uniform hB.1 x i) (filter_subset _ _)
  change (residualMarks B x i).card = 2
  rw [residual_marks_card,hm]

/-- At most one special parent occurrence fits the nine-unit residual budget. -/
theorem minimum_special_count {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hn : Fintype.card ι = 40)
    {x : α} (hx : indexedDegree B x = 13) : (specialIndices B).card ≤ 1 := by
  classical
  have hirr := forty_irredundant hv hB hn
  let L := Multicover.subsetLink B {x}
  let D := residualBlocks B x
  let S := residualSpecials B x
  let M := residualMarks B x
  have hvL : Fintype.card {p : α // p ∉ ({x} : Finset α)} = 13 := by
    rw [Multicover.subset_complement_card,card_singleton,hv]
  have hL := minimum_link_exact hv hB hx
  have hslack := completion_slack hvL hL (residual_completion hB x)
  rw [residual_card,hn,hx] at hslack
  have hc := disjoint_charge_budget (L := L) (B := D) S M
    (residual_charges_disjoint hv hB hirr x)
    (fun i hi T hT => by rw [residual_charge_excess hv hB hirr x hi hT])
  have hl : 5 * S.card ≤ ∑ i ∈ S, (collinearCount L (D i) - 1 + (chargedTriples L (D i) (M i)).card) := by
    calc
      _ = ∑ _i ∈ S, 5 := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum (fun i hi => block_charge_five hvL hL (residual_uniform hB.1 x i)
        (filter_subset _ _) (residual_marks_nonempty hi))
  have hSc : S.card = (specialIndices B).card := residual_specials_card hv hB hx
  change completionLoss L D + completionExcess L D + 234 = 9 * (40-13) at hslack
  omega

end CoveringDesigns.C14_5_3
