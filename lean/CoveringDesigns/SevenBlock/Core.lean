import CoveringDesigns.SevenBlock.Classification

namespace CoveringDesigns.SevenBlock

/-- Expanded actual-covering classification for the general core. The
small Stanton adapter is not needed by this interface. -/
theorem classification_ge_two_expanded {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] {a : ℕ} (ha : 2 ≤ a) (B : I → Finset V)
    (hv : Fintype.card V = 7*a+4) (hi : Fintype.card I = 7)
    (hu : ∀ i, (B i).card = 3*a+2)
    (hc : ∀ T : Finset V, T.card = 2 → ∃ i, T ⊆ B i) :
    ∃ tag : Bool, ∃ e : V ≃ TemplatePoint a tag, ∃ f : I ≃ Fin 7,
      ∀ x i, x ∈ B i ↔ e x ∈ templateBlock a tag (f i) :=
  classification_ge_two ha hv ⟨hu,(Multicover.covers_one_iff B 2).mpr hc⟩ hi

#guard_standard_axioms classification_ge_two_expanded
end CoveringDesigns.SevenBlock

/-! Supported a≥2 classification and its structural prerequisites. Import
this entry when the eleven-point Stanton adapter is not needed. -/
