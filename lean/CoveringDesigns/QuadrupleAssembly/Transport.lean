import CoveringDesigns.QuadrupleAssembly.Contracts

namespace CoveringDesigns.QuadrupleAssembly
open Finset

theorem transverse_map {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (g : α → γ) (h : β → γ) (he : ∀ x, h (e x) = g x)
    (T : Finset α) : Transverse h (T.map e.toEmbedding) ↔ Transverse g T := by
  constructor
  · intro ht x hx y hy hxy
    apply e.injective
    apply ht (mem_map.mpr ⟨x,hx,rfl⟩) (mem_map.mpr ⟨y,hy,rfl⟩)
    simpa only [Equiv.coe_toEmbedding, he] using hxy
  · intro ht x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    apply congrArg e
    apply ht ha hb
    simpa only [Equiv.coe_toEmbedding,he] using hxy

/-- Relabelling the points and their group map preserves exact incidence. -/
theorem GroupDesign.relabel {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    {g : α → γ} {h : β → γ} {C : Family α} {k t : ℕ}
    (hC : GroupDesign g k t C) (e : α ≃ β) (he : ∀ x, h (e x) = g x) :
    GroupDesign h k t (CoveringDesigns.relabel e C) := by
  refine ⟨relabel_uniform e hC.uniform, ?_, ?_⟩
  · intro D hD
    obtain ⟨B,hB,rfl⟩ := mem_map.mp hD
    exact (transverse_map e g h he B).2 (hC.transverse B hB)
  · intro T ht htr
    have he' : ∀ y, g (e.symm y) = h y := by
      intro y
      simpa using (he (e.symm y)).symm
    have hs := (transverse_map e.symm h g he' T).2 htr
    obtain ⟨B,⟨hB,hTB⟩,unique⟩ := hC.exact (T.map e.symm.toEmbedding) (by simpa using ht) hs
    refine ⟨B.map e.toEmbedding, ⟨(mem_relabel e C B).2 hB, map_symm_subset.mp hTB⟩, ?_⟩
    intro D hD
    obtain ⟨E,hE,rfl⟩ := mem_map.mp hD.1
    change E.map e.toEmbedding = B.map e.toEmbedding
    apply congrArg (fun B : Finset α => B.map e.toEmbedding)
    exact unique E ⟨hE,map_symm_subset.mpr hD.2⟩

theorem GroupDesign.of_injective_groups {α β γ : Type*} {g : α → β}
    (f : β → γ) (hf : Function.Injective f) {k t : ℕ} {C : Family α}
    (hC : GroupDesign (f ∘ g) k t C) : GroupDesign g k t C := by
  refine ⟨hC.uniform,?_,?_⟩
  · intro B hB x hx y hy he
    exact hC.transverse B hB hx hy (congrArg f he)
  · intro T ht htr
    apply hC.exact T ht
    intro x hx y hy he
    exact htr hx hy (hf he)

def productFamily {m w : ℕ} (C : Family (Fin (m*w))) : Family (Fin m × Fin w) :=
  CoveringDesigns.relabel finProdFinEquiv.symm C

theorem productFamily_valid {m w k t : ℕ} {C : Family (Fin (m*w))}
    (hC : GroupDesign (fun x : Fin (m*w) => x.val / w) k t C) :
    GroupDesign Prod.fst k t (productFamily C) := by
  apply GroupDesign.of_injective_groups (fun x : Fin m => x.val) Fin.val_injective
  exact hC.relabel finProdFinEquiv.symm (fun _ => rfl)

end CoveringDesigns.QuadrupleAssembly
