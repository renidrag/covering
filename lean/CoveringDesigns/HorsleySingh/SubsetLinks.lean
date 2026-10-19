import CoveringDesigns.Foundations.Links
import CoveringDesigns.Foundations.Intersecting
import CoveringDesigns.Schoenheim.LowerBound

/-! Subset links, including strength zero, for ordinary coverings. -/

namespace CoveringDesigns.HorsleySingh

open Finset
universe u
variable {α : Type u} [DecidableEq α]

/-- Number of blocks containing a specified subset. -/
def multiplicity (C : Family α) (X : Finset α) : ℕ :=
  (C.filter (X ⊆ ·)).card

theorem multiplicity_eq_indexed (C : Family α) (X : Finset α) :
    multiplicity C X = indexedSubsetDegree (fun B : C => B.val) X := by
  simp only [multiplicity, indexedSubsetDegree, card_eq_sum_ones, sum_filter]
  exact (sum_coe_sort C (fun B => if X ⊆ B then (1 : ℕ) else 0)).symm

/-- Delete a subset from every block containing it. -/
def subsetLink (C : Family α) (X : Finset α) : Family {p : α // p ∉ X} :=
  (C.filter (X ⊆ ·)).image (Finset.subtype (· ∉ X))

theorem subsetLink_card (C : Family α) (X : Finset α) :
    (subsetLink C X).card = multiplicity C X := by
  apply card_image_iff.mpr
  intro B hB D hD he
  have hXB := (mem_filter.mp hB).2
  have hXD := (mem_filter.mp hD).2
  ext p
  by_cases hp : p ∈ X
  · exact iff_of_true (hXB hp) (hXD hp)
  · have hh := congrArg (fun T => (⟨p, hp⟩ : {p : α // p ∉ X}) ∈ T) he
    simpa using hh

/-- The link has strength `t-|X|`, also when this is zero. -/
theorem subsetLink_isCover {C : Family α} {k t : ℕ} (h : IsCover C k t)
    (X : Finset α) (hXt : X.card ≤ t) :
    IsCover (subsetLink C X) (k - X.card) (t - X.card) := by
  constructor
  · intro D hD
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hD
    obtain ⟨hBC, hXB⟩ := mem_filter.mp hB
    rw [card_subtype]
    have he : B.filter (· ∉ X) = B \ X := by ext p; simp
    rw [he, card_sdiff_of_subset hXB, h.1 B hBC]
  · intro T hT
    let e : {p : α // p ∉ X} ↪ α := Function.Embedding.subtype _
    have hdis : Disjoint X (T.map e) := by
      apply disjoint_left.mpr
      intro p hp hpm
      obtain ⟨q, _, rfl⟩ := mem_map.mp hpm
      exact q.property hp
    have hc : (X ∪ T.map e).card = t := by
      rw [card_union_of_disjoint hdis, card_map, hT]
      omega
    obtain ⟨B, hBC, hXB⟩ := h.2 _ hc
    refine ⟨B.subtype (· ∉ X), mem_image.mpr ⟨B, ?_, rfl⟩, ?_⟩
    · exact mem_filter.mpr ⟨hBC, fun p hp => hXB (mem_union_left _ hp)⟩
    · intro p hp
      exact mem_subtype.mpr (hXB (mem_union_right _ (mem_map.mpr ⟨p, hp, rfl⟩)))

theorem subset_complement_card [Fintype α] (X : Finset α) :
    Fintype.card {p : α // p ∉ X} = Fintype.card α - X.card := by
  simp [Fintype.card_subtype_compl]

/-- A universal lower bound for families on any finite type in this universe. -/
def CoverLower (v k t b : ℕ) : Prop :=
  ∀ {β : Type u} [Fintype β] [DecidableEq β] {D : Family β},
    Fintype.card β = v → IsCover D k t → b ≤ D.card

theorem multiplicity_ge_of_coverLower [Fintype α] {C : Family α} {v k t i b : ℕ}
    (hn : Fintype.card α = v) (h : IsCover C k t) (hi : i ≤ t)
    (hl : CoverLower.{u} (v-i) (k-i) (t-i) b)
    {X : Finset α} (hX : X.card = i) : b ≤ multiplicity C X := by
  rw [← subsetLink_card]
  apply hl
  · rw [subset_complement_card, hn, hX]
  · simpa only [hX] using subsetLink_isCover h X (by omega)

/-- Schönheim's bound also supplies the conventional strength-zero seed. -/
theorem schoenheim_coverLower {v k t : ℕ} (htk : t ≤ k) (hkv : k ≤ v) :
    CoverLower.{u} v k t (Schoenheim.bound v k t) := by
  intro β _ _ D hn h
  by_cases ht : t = 0
  · subst t
    obtain ⟨B, hB, _⟩ := h.2 ∅ rfl
    exact card_pos.mpr ⟨B, hB⟩
  · simpa only [hn] using Schoenheim.lower_bound (by omega) htk (by omega) h

end CoveringDesigns.HorsleySingh
