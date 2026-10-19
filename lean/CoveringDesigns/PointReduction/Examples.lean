import CoveringDesigns.PointReduction.Family

/-! Boundary checks and four repeated occurrences after point reduction. -/
namespace CoveringDesigns.PointReduction.Examples
open Finset
universe u v w

theorem identity_reduction {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hk : k ≤ Fintype.card α) :
    ∃ B' : ι → Finset α, Multicover.IsCover B' k t lam ∧ B'=B := by
  obtain ⟨B', hB', hp, _⟩ := reduce_along (Function.Embedding.refl α) h hk
  refine ⟨B', hB', ?_⟩
  funext i
  have hs : B i ⊆ B' i := by simpa [pullback] using hp i
  exact (eq_of_subset_of_card_le hs (by rw [hB'.1 i, h.1 i])).symm

theorem strength_zero {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {B : ι → Finset α} {k lam : ℕ} (h : Multicover.IsCover B k 0 lam)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α) :
    ∃ B' : ι → Finset β, Multicover.IsCover B' k 0 lam ∧ lam ≤ Fintype.card ι := by
  obtain ⟨B', hB'⟩ := reduce_points h hk hv
  exact ⟨B', hB', (Multicover.covers_zero_iff B' lam).mp hB'.2⟩

theorem zero_multiplicity {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {B : ι → Finset α} {k t : ℕ} (hu : Multicover.Uniform B k)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α) :
    ∃ B' : ι → Finset β, Multicover.IsCover B' k t 0 :=
  reduce_points ⟨hu, Multicover.covers_multiplicity_zero B t⟩ hk hv

theorem empty_reduction :
    ∃ B' : Fin 0 → Finset (Fin 0), Multicover.IsCover B' 0 0 0 := by
  exact zero_multiplicity (B := fun _ : Fin 0 => (∅ : Finset (Fin 0)))
    (fun _ => rfl) (by simp) (by simp)

def triples (i : Fin 4) : Finset (Fin 4) := univ.erase i

theorem triples_multiplicity (T : Finset (Fin 4)) :
    indexedSubsetDegree triples T=4-T.card := by
  have he : univ.filter (fun i : Fin 4 => T ⊆ triples i)=univ \ T := by
    ext i
    simp [triples, subset_erase]
  unfold indexedSubsetDegree
  rw [he, card_sdiff_of_subset (subset_univ T)]
  simp

theorem triples_cover : Multicover.IsCover triples 3 2 2 := by
  refine ⟨fun i => by simp [triples], ?_⟩
  intro T ht
  rw [triples_multiplicity, ht]

/-- All four original occurrence indices survive, although every resulting block is equal. -/
theorem four_repeated_triples :
    ∃ B' : Fin 4 → Finset (Fin 3), Multicover.IsCover B' 3 2 2 ∧
      (∀ i, B' i=univ) ∧ Fintype.card (Fin 4)=4 ∧
      ∀ T : Finset (Fin 3), indexedSubsetDegree B' T=4 := by
  obtain ⟨B', hB'⟩ := reduce_points (β := Fin 3) triples_cover (by simp) (by simp)
  have he := uniform_full hB'.1 (by simp)
  refine ⟨B', hB', he, by simp, ?_⟩
  intro T
  simp [indexedSubsetDegree, he]

end CoveringDesigns.PointReduction.Examples
