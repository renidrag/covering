import CoveringDesigns.Multicover.Basic

/-! Subset links retain a subtype of the original occurrence indices. -/

namespace CoveringDesigns.Multicover

open Finset
universe u v
variable {α : Type u} {ι : Type v} [DecidableEq α]

def subsetLink (B : ι → Finset α) (X : Finset α) :
    {i // X ⊆ B i} → Finset {p : α // p ∉ X} :=
  fun i => (B i.val).subtype (· ∉ X)

theorem subsetLink_card [Fintype ι] (B : ι → Finset α) (X : Finset α) :
    Fintype.card {i // X ⊆ B i} = indexedSubsetDegree B X :=
  (subsetDegree_eq_card B X).symm

theorem subsetLink_uniform {B : ι → Finset α} {k : ℕ} (h : Uniform B k)
    (X : Finset α) : Uniform (subsetLink B X) (k - X.card) := by
  intro i
  rw [subsetLink, card_subtype]
  have he : (B i.val).filter (· ∉ X) = B i.val \ X := by ext p; simp
  rw [he, card_sdiff_of_subset i.property, h]

/-- The exact residual multiplicity, including repeated blocks and empty subsets. -/
theorem subsetLink_multiplicity [Fintype ι] (B : ι → Finset α) (X : Finset α)
    (T : Finset {p : α // p ∉ X}) :
    indexedSubsetDegree (subsetLink B X) T =
      indexedSubsetDegree B (X ∪ T.map (Function.Embedding.subtype _)) := by
  rw [subsetDegree_eq_card, subsetDegree_eq_card]
  apply Fintype.card_congr
  refine
    { toFun := fun i => ⟨i.val.val, ?_⟩
      invFun := fun i => ⟨⟨i.val, ?_⟩, ?_⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  · apply union_subset i.val.property
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_map.mp hp
    exact mem_subtype.mp (i.property hq)
  · exact fun p hp => i.property (mem_union_left _ hp)
  · intro p hp
    exact mem_subtype.mpr (i.property (mem_union_right _ (mem_map.mpr ⟨p, hp, rfl⟩)))

theorem subsetLink_isCover [Fintype ι] {B : ι → Finset α} {k t lam : ℕ}
    (h : IsCover B k t lam) (X : Finset α) (hXt : X.card ≤ t) :
    IsCover (subsetLink B X) (k - X.card) (t - X.card) lam := by
  refine ⟨subsetLink_uniform h.1 X, ?_⟩
  intro T hT
  rw [subsetLink_multiplicity]
  apply h.2
  have hd : Disjoint X (T.map (Function.Embedding.subtype _)) := by
    apply disjoint_left.mpr
    intro p hp hpm
    obtain ⟨q, _, rfl⟩ := mem_map.mp hpm
    exact q.property hp
  rw [card_union_of_disjoint hd, card_map, hT, Nat.add_sub_of_le hXt]

theorem subset_complement_card [Fintype α] (X : Finset α) :
    Fintype.card {p : α // p ∉ X} = Fintype.card α - X.card := by
  simp [Fintype.card_subtype_compl]

/-- Both point and occurrence universes are arbitrary and independent. -/
def CoverLower (v k t lam b : ℕ) : Prop :=
  ∀ {β : Type u} {κ : Type v} [Fintype β] [DecidableEq β] [Fintype κ]
    {D : κ → Finset β}, Fintype.card β = v → IsCover D k t lam → b ≤ Fintype.card κ

theorem multiplicity_ge_of_coverLower [Fintype α] [Fintype ι]
    {B : ι → Finset α} {v k t lam i b : ℕ}
    (hn : Fintype.card α = v) (h : IsCover B k t lam) (hi : i ≤ t)
    (hl : CoverLower.{u,v} (v-i) (k-i) (t-i) lam b)
    {X : Finset α} (hX : X.card = i) : b ≤ indexedSubsetDegree B X := by
  rw [← subsetLink_card]
  apply hl (D := subsetLink B X)
  · rw [subset_complement_card, hn, hX]
  · simpa only [hX] using subsetLink_isCover h X (by omega)

end CoveringDesigns.Multicover
