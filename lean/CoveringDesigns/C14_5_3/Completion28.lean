import CoveringDesigns.C14_5_3.LowerBound
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

/-! The strengthened completion bound is a consequence of the unconditional
lower bound forty-one. It is never a premise of that lower-bound proof. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v w
variable {α : Type u} {ι : Type v} {κ : Type w}
  [Fintype α] [DecidableEq α] [Fintype ι] [Fintype κ]

def completedBlocks (L : ι → Finset α) (B : κ → Finset α) : (ι ⊕ κ) → Finset (Option α)
  | Sum.inl i => insert none ((L i).map Function.Embedding.some)
  | Sum.inr j => (B j).map Function.Embedding.some

theorem completed_uniform {L : ι → Finset α} {B : κ → Finset α}
    (hL : ExactDesign.IsDesign L 4 2 1) (hB : IsCompletion L B) :
    Multicover.Uniform (completedBlocks L B) 5 := by
  intro i
  cases i with
  | inl i => simp [completedBlocks,hL.1 i]
  | inr j => simp [completedBlocks,hB.1 j]

/-- Triples through the new point are covered by the thirteen augmented lines. -/
theorem completed_covers_new {L : ι → Finset α} (B : κ → Finset α)
    (hL : ExactDesign.IsDesign L 4 2 1) {P : Finset α} (hP : P.card = 2) :
    ∃ i, insert none (P.map Function.Embedding.some) ⊆ completedBlocks L B i := by
  obtain ⟨i,hi,_⟩ := exact_unique_line hL hP
  exact ⟨Sum.inl i,insert_subset_insert none (map_subset_map.mpr hi)⟩

/-- Old collinear triples are covered by the augmented containing line. -/
theorem completed_covers_collinear {L : ι → Finset α} (B : κ → Finset α)
    {T : Finset α} (hT : 0 < indexedSubsetDegree L T) :
    ∃ i, T.map Function.Embedding.some ⊆ completedBlocks L B i := by
  obtain ⟨i,hi⟩ := (multiplicity_pos_iff L T).mp hT
  exact ⟨Sum.inl i,(map_subset_map.mpr hi).trans (subset_insert _ _)⟩

/-- Old noncollinear triples are covered by actual completion occurrences. -/
theorem completed_covers_noncollinear {L : ι → Finset α} {B : κ → Finset α}
    (hB : IsCompletion L B) {T : Finset α} (hT : T.card = 3)
    (hn : indexedSubsetDegree L T = 0) :
    ∃ i, T.map Function.Embedding.some ⊆ completedBlocks L B i := by
  have ht : T ∈ noncollinearTriples L := by simp [noncollinearTriples,hT,hn]
  obtain ⟨i,hi⟩ := (multiplicity_pos_iff B T).mp (by have := hB.2 T ht; omega)
  exact ⟨Sum.inr i,map_subset_map.mpr hi⟩

theorem completed_isCover {L : ι → Finset α} {B : κ → Finset α}
    (hL : ExactDesign.IsDesign L 4 2 1) (hB : IsCompletion L B) :
    Multicover.IsCover (completedBlocks L B) 5 3 1 := by
  classical
  refine ⟨completed_uniform hL hB,(Multicover.covers_one_iff _ _).mpr ?_⟩
  intro T hT
  let U := univ.filter (fun x => some x ∈ T)
  have hsome (x : α) : some x ∈ U.map Function.Embedding.some ↔ some x ∈ T := by simp [U]
  by_cases hn : none ∈ T
  · have he : T = insert none (U.map Function.Embedding.some) := by
      ext x
      cases x with
      | none => simp [hn]
      | some x => simpa using (hsome x).symm
    have hU : U.card = 2 := by rw [he] at hT; simp at hT; omega
    simpa [he] using completed_covers_new B hL hU
  · have he : T = U.map Function.Embedding.some := by
      ext x
      cases x with
      | none => simp [hn]
      | some x => exact (hsome x).symm
    have hU : U.card = 3 := by simpa [he] using hT
    by_cases hc : 0 < indexedSubsetDegree L U
    · simpa [he] using completed_covers_collinear B hc
    · have hc0 : indexedSubsetDegree L U = 0 := by omega
      simpa [he] using completed_covers_noncollinear hB hU hc0

/-- Universal strengthened completion theorem for indexed five-subsets.
Repetitions are allowed; only noncollinear triples need to be covered. -/
theorem completion_at_least_28 {L : ι → Finset α} {B : κ → Finset α}
    (hv : Fintype.card α = 13) (hL : ExactDesign.IsDesign L 4 2 1)
    (hB : IsCompletion L B) : 28 ≤ Fintype.card κ := by
  have hc := indexed_lower_bound (B := completedBlocks L B)
    (by simp [hv]) (completed_isCover hL hB)
  rw [Fintype.card_sum,exact_line_count hv hL] at hc
  omega

end CoveringDesigns.C14_5_3
