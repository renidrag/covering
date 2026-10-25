import CoveringDesigns.SevenBlock.Core
import CoveringDesigns.SevenBlock.Stanton

/-! The complete seven-block classification, including the a=1 adapter. -/
namespace CoveringDesigns.SevenBlock
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Exactly one of the two weighted Fano forms occurs for every a≥1.
The point equivalence retains distinct points with coincident supports. -/
theorem classification {a : ℕ} (ha : 1 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) :
    ∃! tag : Bool, IndexedIsomorphic B (templateBlock a tag) := by
  have hex : ∃ tag : Bool, IndexedIsomorphic B (templateBlock a tag) := by
    by_cases he : a = 1
    · subst a
      exact classification_one (by simpa using hv) (by simpa using h) hi
    · exact classification_ge_two (by omega) hv h hi
  obtain ⟨tag,htag⟩ := hex
  refine ⟨tag,htag,?_⟩
  intro other hother
  by_contra hn
  have hbad := htag.symm.trans hother
  cases tag <;> cases other
  · exact hn rfl
  · exact templates_not_isomorphic a hbad
  · exact templates_not_isomorphic a hbad.symm
  · exact hn rfl

/-- Expanded finite covering contract, with no shorthand covering or
isomorphism premise and no injectivity assumption. -/
theorem classification_expanded {a : ℕ} (ha : 1 ≤ a) (B : I → Finset V)
    (hv : Fintype.card V = 7*a+4) (hi : Fintype.card I = 7)
    (hu : ∀ i, (B i).card = 3*a+2)
    (hc : ∀ T : Finset V, T.card = 2 → ∃ i, T ⊆ B i) :
    ∃! tag : Bool, ∃ e : V ≃ TemplatePoint a tag, ∃ f : I ≃ Fin 7,
      ∀ x i, x ∈ B i ↔ e x ∈ templateBlock a tag (f i) :=
  classification ha hv ⟨hu,(Multicover.covers_one_iff B 2).mpr hc⟩ hi

#guard_standard_axioms classification classification_expanded

end CoveringDesigns.SevenBlock
