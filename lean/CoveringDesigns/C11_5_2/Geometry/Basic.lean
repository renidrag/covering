import CoveringDesigns.Foundations.StarRelabelling
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Union

/-! Intrinsic terminology and the marked-couple coordinates used by GPPT.
These definitions and transport lemmas apply to arbitrary finite families. -/

namespace CoveringDesigns.StantonGeometry

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def multiplicity (C : Family α) (T : Finset α) : ℕ :=
  (C.filter (T ⊆ ·)).card

def IsCouple (C : Family α) (K : Finset α) : Prop :=
  K.card = 2 ∧ 3 ≤ multiplicity C K

instance (C : Family α) (K : Finset α) : Decidable (IsCouple C K) :=
  inferInstanceAs (Decidable (K.card = 2 ∧ 3 ≤ multiplicity C K))

def coupleCount (C : Family α) (B : Finset α) : ℕ :=
  ((B.powersetCard 2).filter (IsCouple C)).card

def IsShortBlock (C : Family α) (B : Finset α) : Prop :=
  B ∈ C ∧ coupleCount C B ≤ 1

instance (C : Family α) (B : Finset α) : Decidable (IsShortBlock C B) :=
  inferInstanceAs (Decidable (B ∈ C ∧ coupleCount C B ≤ 1))

def IsShortPoint (C : Family α) (x : α) : Prop :=
  degree C x = 3 ∧ ∃ B ∈ C, IsShortBlock C B ∧ x ∈ B

instance (C : Family α) (x : α) : Decidable (IsShortPoint C x) :=
  inferInstanceAs (Decidable (degree C x = 3 ∧ ∃ B ∈ C, IsShortBlock C B ∧ x ∈ B))

def markedRow (T : Fin 3 → Finset α) (s : Fin 3 → α) (i : Fin 3) : Finset α :=
  {s i} ∪ ((univ.erase i).biUnion fun j => T j \ {s j})

structure MarkingFrame [Fintype α] (C : Family α) (K : Finset α) where
  triads : Fin 3 → Finset α
  selected : Fin 3 → α
  shortBlock : Finset α
  couple_card : K.card = 2
  triad_card : ∀ i, (triads i).card = 3
  triads_disjoint : Pairwise fun i j => Disjoint (triads i) (triads j)
  triads_union : univ.biUnion triads = univ \ K
  selected_mem : ∀ i, selected i ∈ triads i
  shortBlock_card : shortBlock.card = 5
  selected_subset : univ.image selected ⊆ shortBlock
  short_iff : ∀ B, IsShortBlock C B ↔ B = shortBlock
  selected_iff : ∀ x, x ∈ univ.image selected ↔ IsShortPoint C x
  blocks_eq : C = insert shortBlock
    ((univ.image fun i => K ∪ triads i) ∪ (univ.image (markedRow triads selected)))

theorem multiplicity_relabel (e : α ≃ β) (C : Family α) (T : Finset α) :
    multiplicity (relabel e C) (T.map e.toEmbedding) = multiplicity C T := by
  unfold multiplicity relabel
  rw [filter_map, card_map]
  congr 1
  ext B
  simp

@[simp] theorem isCouple_relabel (e : α ≃ β) (C : Family α) (T : Finset α) :
    IsCouple (relabel e C) (T.map e.toEmbedding) ↔ IsCouple C T := by
  simp [IsCouple, multiplicity_relabel]

theorem coupleCount_relabel (e : α ≃ β) (C : Family α) (B : Finset α) :
    coupleCount (relabel e C) (B.map e.toEmbedding) = coupleCount C B := by
  unfold coupleCount
  rw [powersetCard_map, filter_map, card_map]
  congr 1
  ext T
  simp

@[simp] theorem isShortBlock_relabel (e : α ≃ β) (C : Family α) (B : Finset α) :
    IsShortBlock (relabel e C) (B.map e.toEmbedding) ↔ IsShortBlock C B := by
  simp [IsShortBlock, coupleCount_relabel]

@[simp] theorem isShortPoint_relabel (e : α ≃ β) (C : Family α) (x : α) :
    IsShortPoint (relabel e C) (e x) ↔ IsShortPoint C x := by
  simp only [IsShortPoint, degree_relabel]
  constructor
  · rintro ⟨hd, B, hB, hs, hx⟩
    obtain ⟨D, hD, rfl⟩ := mem_map.mp hB
    exact ⟨hd, D, hD, (isShortBlock_relabel e C D).mp hs, by simpa using hx⟩
  · rintro ⟨hd, B, hB, hs, hx⟩
    exact ⟨hd, B.map e.toEmbedding, (mem_relabel e C B).mpr hB,
      (isShortBlock_relabel e C B).mpr hs, by simpa using hx⟩

theorem map_biUnion {ι : Type*} [DecidableEq ι] (e : α ≃ β)
    (I : Finset ι) (T : ι → Finset α) :
    (I.biUnion T).map e.toEmbedding = I.biUnion (fun i => (T i).map e.toEmbedding) := by
  simp only [map_eq_image, biUnion_image]

theorem relabel_image {ι : Type*} (e : α ≃ β) (I : Finset ι) (T : ι → Finset α) :
    relabel e (I.image T) = I.image (fun i => (T i).map e.toEmbedding) := by
  simp only [relabel, map_eq_image, image_image]
  congr 1
  funext i
  exact map_eq_image e.toEmbedding (T i)

theorem markedRow_map (e : α ≃ β) (T : Fin 3 → Finset α) (s : Fin 3 → α) (i : Fin 3) :
    (markedRow T s i).map e.toEmbedding =
      markedRow (fun j => (T j).map e.toEmbedding) (fun j => e (s j)) i := by
  simp only [markedRow, map_union, map_singleton, map_biUnion, map_sdiff]
  rfl

def MarkingFrame.relabel [Fintype α] [Fintype β]
    {C : Family α} {K : Finset α} (F : MarkingFrame C K) (e : α ≃ β) :
    MarkingFrame (CoveringDesigns.relabel e C) (K.map e.toEmbedding) where
  triads i := (F.triads i).map e.toEmbedding
  selected i := e (F.selected i)
  shortBlock := F.shortBlock.map e.toEmbedding
  couple_card := by simpa using F.couple_card
  triad_card i := by simpa using F.triad_card i
  triads_disjoint i j hij := by simpa using F.triads_disjoint hij
  triads_union := by
    rw [← map_biUnion, F.triads_union, map_sdiff]
    simp
  selected_mem i := by simpa using F.selected_mem i
  shortBlock_card := by simpa using F.shortBlock_card
  selected_subset := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    simpa using F.selected_subset (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  short_iff B := by
    obtain ⟨D, rfl⟩ := (Equiv.finsetCongr e).surjective B
    simpa only [Equiv.finsetCongr_apply, isShortBlock_relabel, map_inj] using F.short_iff D
  selected_iff x := by
    obtain ⟨y, rfl⟩ := e.surjective x
    simpa only [mem_image, mem_univ, true_and, e.injective.eq_iff,
      isShortPoint_relabel] using F.selected_iff y
  blocks_eq := by
    conv_lhs => rw [F.blocks_eq]
    simp only [CoveringDesigns.relabel, map_insert, map_union]
    congr 1
    change CoveringDesigns.relabel e (univ.image fun i => K ∪ F.triads i) ∪
        CoveringDesigns.relabel e (univ.image (markedRow F.triads F.selected)) = _
    rw [relabel_image, relabel_image]
    simp only [map_union, markedRow_map]

#guard_standard_axioms multiplicity_relabel coupleCount_relabel isShortBlock_relabel
  isShortPoint_relabel MarkingFrame.relabel

end CoveringDesigns.StantonGeometry
