import CoveringDesigns.Foundations.Basic

/-! Relabelling preserves the mathematical covering problem. -/

namespace CoveringDesigns

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def relabel (e : α ≃ β) (C : Family α) : Family β :=
  C.map (Finset.mapEmbedding e.toEmbedding).toEmbedding

omit [DecidableEq α] [DecidableEq β] in
theorem relabel_card (e : α ≃ β) (C : Family α) :
    (relabel e C).card = C.card := card_map _

omit [DecidableEq α] [DecidableEq β] in
@[simp] theorem mem_relabel (e : α ≃ β) (C : Family α) (B : Finset α) :
    B.map e.toEmbedding ∈ relabel e C ↔ B ∈ C := by
  exact mem_map' _

omit [DecidableEq α] [DecidableEq β] in
theorem relabel_uniform (e : α ≃ β) {C : Family α} {k : ℕ}
    (h : Uniform C k) : Uniform (relabel e C) k := by
  intro D hD
  obtain ⟨B, hB, rfl⟩ := mem_map.mp hD
  simpa using h B hB

theorem relabel_covers (e : α ≃ β) {C : Family α} {t : ℕ}
    (h : Covers C t) : Covers (relabel e C) t := by
  intro T hT
  obtain ⟨B, hB, hs⟩ := h (T.map e.symm.toEmbedding) (by simpa using hT)
  refine ⟨B.map e.toEmbedding, (mem_relabel e C B).mpr hB, ?_⟩
  exact (map_symm_subset).mp hs

theorem relabel_isCover (e : α ≃ β) {C : Family α} {k t : ℕ}
    (h : IsCover C k t) : IsCover (relabel e C) k t :=
  ⟨relabel_uniform e h.1, relabel_covers e h.2⟩

theorem star_relabel (e : α ≃ β) (C : Family α) (p : α) :
    star (relabel e C) (e p) = relabel e (star C p) := by
  unfold star relabel
  rw [filter_map]
  congr 1
  ext B
  simp [Function.comp_def]

theorem degree_relabel (e : α ≃ β) (C : Family α) (p : α) :
    degree (relabel e C) (e p) = degree C p := by
  unfold degree
  rw [star_relabel, relabel_card]

def Isomorphic (C : Family α) (D : Family β) : Prop :=
  ∃ e : α ≃ β, relabel e C = D

omit [DecidableEq α] [DecidableEq β] in
theorem relabel_trans {γ : Type*} (e : α ≃ β) (f : β ≃ γ)
    (C : Family α) : relabel f (relabel e C) = relabel (e.trans f) C := by
  unfold relabel
  simp only [map_map]
  congr 1
  apply Function.Embedding.ext
  intro B
  change (B.map e.toEmbedding).map f.toEmbedding = B.map (e.trans f).toEmbedding
  exact map_map _ _ _

theorem isomorphic_of_image [Fintype α] (f : α → α) (hf : Function.Injective f)
    {C D : Family α} (h : C.image (fun B => B.image f) = D) : Isomorphic C D := by
  let e : α ≃ α := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨e, ?_⟩
  unfold relabel
  rw [map_eq_image]
  change C.image (fun B => B.map e.toEmbedding) = D
  have he : (e.toEmbedding : α → α) = f := rfl
  simpa only [map_eq_image, he] using h

theorem Isomorphic.trans {γ : Type*} [DecidableEq γ]
    {C : Family α} {D : Family β} {E : Family γ}
    (h : Isomorphic C D) (g : Isomorphic D E) : Isomorphic C E := by
  obtain ⟨e, rfl⟩ := h
  obtain ⟨f, hf⟩ := g
  exact ⟨e.trans f, (relabel_trans e f C).symm.trans hf⟩

theorem Isomorphic.card_eq {C : Family α} {D : Family β} (h : Isomorphic C D) :
    C.card = D.card := by
  obtain ⟨e, rfl⟩ := h
  exact (relabel_card e C).symm

theorem Isomorphic.isCover {C : Family α} {D : Family β} {k t : ℕ}
    (h : Isomorphic C D) (hc : IsCover C k t) : IsCover D k t := by
  obtain ⟨e, rfl⟩ := h
  exact relabel_isCover e hc

end CoveringDesigns
