import CoveringDesigns.SevenBlock.Templates
import CoveringDesigns.C11_5_2.Classification

/-! Only the a=1 adapter imports the unchanged ordinary Stanton theorem.
The general a≥2 branch and the nineteen-point application must not import
this module. The empty Type-II fibre is included by the actual templates. -/
namespace CoveringDesigns.SevenBlock
open Finset

private theorem iso_symm {V W : Type*} [DecidableEq V] [DecidableEq W]
    {C : Family V} {D : Family W} (h : Isomorphic C D) : Isomorphic D C := by
  obtain ⟨e,he⟩ := h
  exact ⟨e.symm, by rw [← he, relabel_symm_relabel]⟩

private theorem template_families_separate :
    ¬ Isomorphic (templateFamily 1 false) (templateFamily 1 true) := by
  intro h
  exact templates_not_isomorphic 1
    (ordinary_isomorphism_to_indexed (template_injective (by decide) false)
      (template_injective (by decide) true) h)

/-- Stanton's two ordinary classes imply exhaustion by our two explicit,
nonisomorphic templates, without assuming how Stanton names those classes. -/
theorem classification_one {V I : Type*}
    [Fintype V] [DecidableEq V] [Fintype I] {B : I → Finset V}
    (hv : Fintype.card V = 11) (h : Multicover.IsCover B 5 2 1)
    (hi : Fintype.card I = 7) :
    ∃ tag, IndexedIsomorphic B (templateBlock 1 tag) := by
  have hB := blocks_injective (a := 1) (by decide) hv h hi
  have hc := (Multicover.deduplicate_isCover_one B 5 2).mpr h
  have hn : (Multicover.deduplicate B).card = 7 := by
    rw [Multicover.deduplicate, card_image_of_injective _ hB, card_univ, hi]
  obtain ⟨t,ht⟩ := stanton_classification_on hv hc hn
  obtain ⟨t₀,h₀⟩ := stanton_classification_on
    (template_point_card (a := 1) (by decide) false)
    (template_family_isCover (a := 1) (by decide) false)
    (template_family_card (a := 1) (by decide) false)
  obtain ⟨t₁,h₁⟩ := stanton_classification_on
    (template_point_card (a := 1) (by decide) true)
    (template_family_isCover (a := 1) (by decide) true)
    (template_family_card (a := 1) (by decide) true)
  have hne : t₀ ≠ t₁ := by
    intro he
    subst t₁
    exact template_families_separate (h₀.trans (iso_symm h₁))
  have htchoice : t = t₀ ∨ t = t₁ := by cases t <;> cases t₀ <;> cases t₁ <;> simp_all
  rcases htchoice with rfl | rfl
  · exact ⟨false, ordinary_isomorphism_to_indexed hB
      (template_injective (a := 1) (by decide) false) (ht.trans (iso_symm h₀))⟩
  · exact ⟨true, ordinary_isomorphism_to_indexed hB
      (template_injective (a := 1) (by decide) true) (ht.trans (iso_symm h₁))⟩

#guard_standard_axioms classification_one

end CoveringDesigns.SevenBlock
