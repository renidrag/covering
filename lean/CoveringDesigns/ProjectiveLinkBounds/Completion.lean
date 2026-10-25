import CoveringDesigns.ProjectiveLinkBounds.Parity

/-! Completion charges retain actual occurrence indices, including all extra
occurrences through the distinguished point. -/
namespace CoveringDesigns.ProjectiveLinkBounds
open Finset Internal
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

def pointTrace (B : ι → Finset α) (x : α) (i : ι) : Finset {p : α // p ∉ ({x} : Finset α)} :=
  (B i).subtype (· ∉ ({x} : Finset α))

def noncollinearTriples (L : ι → Finset α) : Finset (Finset α) :=
  (univ.powersetCard 3).filter (fun T => indexedSubsetDegree L T = 0)

private theorem triple_partition (L : ι → Finset α) (A : Finset α) :
    (collinearTriples L A).card +
      ((noncollinearTriples L).filter (· ⊆ A)).card = A.card.choose 3 := by
  have h := card_filter_add_card_filter_not (s := A.powersetCard 3)
    (fun T => 0 < indexedSubsetDegree L T)
  have he : (A.powersetCard 3).filter (fun T => ¬ 0 < indexedSubsetDegree L T) =
      (noncollinearTriples L).filter (· ⊆ A) := by
    ext T
    simp [noncollinearTriples, mem_powersetCard, and_comm, and_left_comm, and_assoc]
  rw [he] at h
  simpa only [collinearTriples, card_powersetCard] using h

theorem noncollinear_card {q : ℕ} (hq : 3 ≤ q) {L : ι → Finset α}
    (hv : Fintype.card α = pointCount q) (hL : ExactDesign.IsDesign L (q+1) 2 1) :
    (noncollinearTriples L).card = tripleDemand q := by
  have hs := triple_partition L univ
  have hc : (collinearTriples L univ).card = pointCount q*(q+1).choose 3 := by
    rw [collinear_count hL]
    simp only [inter_univ]
    rw [sum_const_nat (fun i _ => congrArg (fun n => n.choose 3) (hL.1 i)),
      card_univ, exact_line_count (by omega) hv hL]
  simp only [hc, filter_true_of_mem (fun _ _ => subset_univ _), card_univ, hv] at hs
  have hd := demand_balance q
  omega

private theorem noncollinear_capacity {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {L : ι → Finset α} (hv : Fintype.card α = pointCount q)
    (hL : ExactDesign.IsDesign L (q+1) 2 1)
    {A : Finset α} (hA : A.card = q+1 ∨ A.card = q+2) :
    ((noncollinearTriples L).filter (· ⊆ A)).card ≤ capacity q := by
  have hs := triple_partition L A
  rcases hA with ha | ha
  · rw [ha] at hs
    exact (by omega : ((noncollinearTriples L).filter (· ⊆ A)).card ≤ (q+1).choose 3)
      |>.trans (capacity_ge hq)
  · have hl := collinear_lower_bound hq ho hv hL ha
    have hb := capacity_balance hq
    rw [ha] at hs
    omega

private theorem trace_card {B : ι → Finset α} {q : ℕ}
    (hu : Multicover.Uniform B (q+2)) (x : α) (i : ι) :
    (pointTrace B x i).card = q+1 ∨ (pointTrace B x i).card = q+2 := by
  have he : (pointTrace B x i).card = ((B i).erase x).card := by
    rw [pointTrace, card_subtype]
    congr 1
    ext y
    simp [and_comm]
  rw [he]
  by_cases hx : x ∈ B i
  · left; rw [card_erase_of_mem hx, hu i]; omega
  · right; rw [erase_eq_of_notMem hx, hu i]

private theorem trace_covers {B : ι → Finset α} {q : ℕ}
    (hB : Multicover.IsCover B (q+2) 3 1) (x : α)
    {T : Finset {p : α // p ∉ ({x} : Finset α)}} (hT : T.card = 3) :
    ∃ i, T ⊆ pointTrace B x i := by
  have hm := hB.2 (T.map (Function.Embedding.subtype _)) (by simpa using hT)
  have hm' : 0 < indexedSubsetDegree B (T.map (Function.Embedding.subtype _)) := by omega
  obtain ⟨i,hi⟩ := (multiplicity_pos_iff B _).mp hm'
  refine ⟨i, ?_⟩
  intro y hy
  apply mem_subtype.mpr
  exact hi (mem_map.mpr ⟨y,hy,rfl⟩)

/-- A selected set of original indices forms the plane; additional indices
through x are not discarded and have their own (smaller) trace capacity. -/
theorem completion_count {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {B : ι → Finset α} (hv : Fintype.card α = pointCount q+1)
    (hB : Multicover.IsCover B (q+2) 3 1) (x : α) (J : Finset ι)
    (hJ : ∀ j ∈ J, x ∈ B j)
    (hL : ExactDesign.IsDesign (fun j : J => pointTrace B x j.val) (q+1) 2 1) :
    tripleDemand q ≤ (Fintype.card ι-pointCount q)*capacity q := by
  classical
  let L := fun j : J => pointTrace B x j.val
  let D := noncollinearTriples L
  let R := fun i : {i // i ∉ J} => pointTrace B x i.val
  have hw : Fintype.card {p : α // p ∉ ({x} : Finset α)} = pointCount q := by
    rw [Multicover.subset_complement_card, card_singleton, hv]
    omega
  have hjc : J.card = pointCount q := by
    simpa using exact_line_count (by omega) hw hL
  have hdc : D.card = tripleDemand q := noncollinear_card hq hw hL
  have hr (T : Finset {p : α // p ∉ ({x} : Finset α)}) (hT : T ∈ D) :
      1 ≤ indexedSubsetDegree R T := by
    obtain ⟨ht,hzero⟩ := mem_filter.mp hT
    obtain ⟨i,hi⟩ := trace_covers hB x (mem_powersetCard.mp ht).2
    have hij : i ∉ J := by
      intro hij
      have hh := (multiplicity_pos_iff L T).mpr ⟨⟨i,hij⟩,hi⟩
      omega
    exact (multiplicity_pos_iff R T).mpr ⟨⟨i,hij⟩,hi⟩
  have hs := sum_le_sum hr
  rw [selected_subset_count] at hs
  have hc := sum_le_sum (s := (univ : Finset {i // i ∉ J}))
    (fun i _ => noncollinear_capacity hq ho hw hL (trace_card hB.1 x i.val))
  have hrc : Fintype.card {i // i ∉ J} = Fintype.card ι-pointCount q := by
    rw [Fintype.card_subtype_compl]
    simp [hjc]
  have ht := hs.trans hc
  simpa only [sum_const, Nat.nsmul_eq_mul, mul_one, card_univ, hdc, hrc, Nat.mul_comm]
    using ht

theorem completion_bound {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {B : ι → Finset α} (hv : Fintype.card α = pointCount q+1)
    (hB : Multicover.IsCover B (q+2) 3 1) (x : α) (J : Finset ι)
    (hJ : ∀ j ∈ J, x ∈ B j)
    (hL : ExactDesign.IsDesign (fun j : J => pointTrace B x j.val) (q+1) 2 1) :
    pointCount q + Schoenheim.ceilDiv (tripleDemand q) (capacity q) ≤ Fintype.card ι := by
  classical
  have hw : Fintype.card {p : α // p ∉ ({x} : Finset α)} = pointCount q := by
    rw [Multicover.subset_complement_card, card_singleton, hv]; omega
  have hjc : J.card = pointCount q := by
    simpa using exact_line_count (by omega) hw hL
  have hn : pointCount q ≤ Fintype.card ι := by
    simpa [hjc] using card_le_card (subset_univ J)
  have h : Schoenheim.ceilDiv (tripleDemand q) (capacity q) ≤ Fintype.card ι-pointCount q :=
    (Schoenheim.ceilDiv_le_iff (capacity_pos hq)).mpr
    (by simpa [Nat.mul_comm] using completion_count hq ho hv hB x J hJ hL)
  omega

namespace Internal

theorem completion_of_link_selection {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {B : ι → Finset α} (hv : Fintype.card α = pointCount q+1)
    (hB : Multicover.IsCover B (q+2) 3 1) (x : α)
    (K : Finset {i // ({x} : Finset α) ⊆ B i})
    (hK : ExactDesign.IsDesign (fun j : K => Multicover.subsetLink B {x} j.val) (q+1) 2 1) :
    tripleDemand q ≤ (Fintype.card ι-pointCount q)*capacity q ∧
      pointCount q + Schoenheim.ceilDiv (tripleDemand q) (capacity q) ≤ Fintype.card ι := by
  classical
  let J := K.map (Function.Embedding.subtype _)
  let e := K.equivMap (Function.Embedding.subtype _)
  have hj (i : ι) (hi : i ∈ J) : x ∈ B i := by
    obtain ⟨j,_,rfl⟩ := mem_map.mp hi
    exact j.property (mem_singleton_self x)
  have hL : ExactDesign.IsDesign (fun j : J => pointTrace B x j.val) (q+1) 2 1 := by
    constructor
    · intro j
      obtain ⟨k,rfl⟩ := e.surjective j
      exact hK.1 k
    · intro T hT
      rw [← Multicover.subsetDegree_reindex e]
      exact hK.2 T hT
  exact ⟨completion_count hq ho hv hB x J hj hL, completion_bound hq ho hv hB x J hj hL⟩

theorem completion_of_exact_link {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {B : ι → Finset α} (hv : Fintype.card α = pointCount q+1)
    (hB : Multicover.IsCover B (q+2) 3 1) (x : α)
    (hd : indexedDegree B x = pointCount q) :
    tripleDemand q ≤ (Fintype.card ι-pointCount q)*capacity q ∧
      pointCount q + Schoenheim.ceilDiv (tripleDemand q) (capacity q) ≤ Fintype.card ι := by
  classical
  have hw : Fintype.card {p : α // p ∉ ({x} : Finset α)} = pointCount q := by
    rw [Multicover.subset_complement_card,card_singleton,hv]; omega
  have hl : Multicover.IsCover (Multicover.subsetLink B {x}) (q+1) 2 1 := by
    simpa using Multicover.subsetLink_isCover hB {x} (by simp)
  have hc : Fintype.card {i // ({x} : Finset α) ⊆ B i} = pointCount q := by
    rw [Multicover.subsetLink_card,Multicover.subsetDegree_singleton,hd]
  have he := pair_cover_exact (by omega) hw hl hc
  apply completion_of_link_selection hq ho hv hB x univ
  refine ⟨fun j => he.1 j.val, ?_⟩
  intro T hT
  rw [restrict_multiplicity]
  simpa [indexedSubsetDegree] using he.2 T hT

theorem parent_degree_floor {q : ℕ} (hq : 3 ≤ q)
    {B : ι → Finset α} (hv : Fintype.card α = pointCount q+1)
    (hB : Multicover.IsCover B (q+2) 3 1) (x : α) : pointCount q ≤ indexedDegree B x := by
  have hw : Fintype.card {p : α // p ∉ ({x} : Finset α)} = pointCount q := by
    rw [Multicover.subset_complement_card,card_singleton,hv]; omega
  have hl : Multicover.IsCover (Multicover.subsetLink B {x}) (q+1) 2 1 := by
    simpa using Multicover.subsetLink_isCover hB {x} (by simp)
  simpa only [Multicover.subsetLink_card,Multicover.subsetDegree_singleton] using
    pair_cover_lower (by omega) hw hl

end Internal
end CoveringDesigns.ProjectiveLinkBounds
