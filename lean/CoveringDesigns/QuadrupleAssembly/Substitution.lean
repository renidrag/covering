import CoveringDesigns.QuadrupleAssembly.FiniteChecks
import Mathlib.Data.Finset.Preimage

namespace CoveringDesigns.QuadrupleAssembly
open Finset

/-- The exact local contract required when a master block is replaced. -/
structure PatchContract {α β : Type*} [DecidableEq α] [DecidableEq β]
    (π : α → β) (B : Finset β) (k t : ℕ) (L : Family α) : Prop where
  uniform : Uniform L k
  transverse : ∀ D ∈ L, Transverse π D
  support : ∀ D ∈ L, D.image π ⊆ B
  exact : ∀ T : Finset α, T.card = t → Transverse π T → T.image π ⊆ B →
    ∃! D, D ∈ L ∧ T ⊆ D

/-- Constant-weight block substitution, with a possibly mixed-size master. -/
theorem substitute {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (π : α → β) (g : β → γ) {t k : ℕ} {M : Family β} (hM : Master g t M)
    (L : Finset β → Family α) (hL : ∀ B ∈ M, PatchContract π B k t (L B)) :
    GroupDesign (g ∘ π) k t (M.biUnion L) := by
  refine ⟨?_,?_,?_⟩
  · intro D hD
    obtain ⟨B,hB,hD⟩ := mem_biUnion.mp hD
    exact (hL B hB).uniform D hD
  · intro D hD x hx y hy he
    obtain ⟨B,hB,hD⟩ := mem_biUnion.mp hD
    apply (hL B hB).transverse D hD hx hy
    exact hM.transverse B hB
      ((hL B hB).support D hD (mem_image.mpr ⟨x,hx,rfl⟩))
      ((hL B hB).support D hD (mem_image.mpr ⟨y,hy,rfl⟩)) he
  · intro T hT ht
    have hp : Transverse π T := by
      intro x hx y hy he
      exact ht hx hy (congrArg g he)
    have hg : Transverse g (T.image π) := by
      intro x hx y hy he
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      exact congrArg π (ht ha hb he)
    have hcard : (T.image π).card = t := (card_image_iff.mpr hp).trans hT
    obtain ⟨B,⟨hB,hs⟩,uniqB⟩ := hM.exact (T.image π) hcard hg
    obtain ⟨D,⟨hD,hTD⟩,uniqD⟩ := (hL B hB).exact T hT hp hs
    refine ⟨D,⟨mem_biUnion.mpr ⟨B,hB,hD⟩,hTD⟩,?_⟩
    intro E hE
    obtain ⟨U,hU,hEU⟩ := mem_biUnion.mp hE.1
    have hsU : T.image π ⊆ U := (image_subset_image hE.2).trans ((hL U hU).support E hEU)
    have hu := uniqB U ⟨hU,hsU⟩
    subst U
    exact uniqD E ⟨hEU,hE.2⟩

/-- Embed a local group design into one master block. The range hypothesis
says exactly which enlarged points belong to that block. -/
theorem patch_of_embedding {α β δ γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq δ] (π : α → β) (B : Finset β) (e : δ ↪ α)
    (g : δ → γ) (j : γ ↪ β) (he : ∀ x, π (e x) = j (g x))
    (hr : ∀ x, π x ∈ B ↔ x ∈ Set.range e)
    {k t : ℕ} {C : Family δ} (hC : GroupDesign g k t C) :
    PatchContract π B k t (C.image (fun D => D.map e)) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro D hD
    obtain ⟨E,hE,rfl⟩ := mem_image.mp hD
    simpa using hC.uniform E hE
  · intro D hD x hx y hy hxy
    obtain ⟨E,hE,rfl⟩ := mem_image.mp hD
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    apply congrArg e
    apply hC.transverse E hE ha hb
    apply j.injective
    simpa only [he] using hxy
  · intro D hD x hx
    obtain ⟨E,hE,rfl⟩ := mem_image.mp hD
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hy
    exact (hr (e z)).2 ⟨z,rfl⟩
  · intro T hT ht hs
    let S := T.preimage e e.injective.injOn
    have hm : S.map e = T := by
      ext x
      constructor
      · rintro hx
        obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
        exact mem_preimage.mp hy
      · intro hx
        obtain ⟨y,rfl⟩ := (hr x).1 (hs (mem_image.mpr ⟨x,hx,rfl⟩))
        exact mem_map.mpr ⟨y,mem_preimage.mpr hx,rfl⟩
    have hsc : S.card = t := by rw [← card_map e,hm,hT]
    have hst : Transverse g S := by
      intro x hx y hy heq
      apply e.injective
      apply ht (mem_preimage.mp hx) (mem_preimage.mp hy)
      rw [he,he,heq]
    obtain ⟨D,⟨hD,hSD⟩,unique⟩ := hC.exact S hsc hst
    refine ⟨D.map e,⟨mem_image.mpr ⟨D,hD,rfl⟩,?_⟩,?_⟩
    · rw [← hm]
      exact map_subset_map.mpr hSD
    · intro E hE
      obtain ⟨U,hU,rfl⟩ := mem_image.mp hE.1
      apply congrArg (fun D : Finset δ => D.map e)
      apply unique U
      refine ⟨hU,?_⟩
      have hh := hE.2
      rw [← hm] at hh
      exact map_subset_map.mp hh

end CoveringDesigns.QuadrupleAssembly
