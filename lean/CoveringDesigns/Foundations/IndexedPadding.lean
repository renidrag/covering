import CoveringDesigns.Multicover.Basic
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Fintype.Sum

/-! Padding occurrence counts by repeating an actual block. Empty covers
are excluded from a positive-multiplicity contract on an existing t-subset.
There is no assumption of distinct block images. -/
namespace CoveringDesigns.IndexedPadding
open Finset
universe u v

theorem nonempty_occurrences {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] {B : I → Finset V} {k t : ℕ}
    (ht : t ≤ Fintype.card V) (h : Multicover.IsCover B k t 1) : Nonempty I := by
  obtain ⟨T, _, hT⟩ := exists_subset_card_eq (show t ≤ (univ : Finset V).card by simpa using ht)
  obtain ⟨i, _⟩ := (Multicover.covers_one_iff B t).mp h.2 T hT
  exact ⟨i⟩

/-- Add exactly enough copies of one chosen occurrence to reach `b`. -/
theorem pad {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] {B : I → Finset V} {k t b : ℕ}
    (ht : t ≤ Fintype.card V) (h : Multicover.IsCover B k t 1)
    (hb : Fintype.card I ≤ b) :
    ∃ D : Fin b → Finset V, Multicover.IsCover D k t 1 := by
  classical
  obtain ⟨i₀⟩ := nonempty_occurrences ht h
  let C : I ⊕ Fin (b - Fintype.card I) → Finset V := Sum.elim B (fun _ => B i₀)
  have hc : Multicover.IsCover C k t 1 := by
    constructor
    · intro j
      cases j with
      | inl i => exact h.1 i
      | inr _ => exact h.1 i₀
    · rw [Multicover.covers_one_iff]
      intro T hT
      obtain ⟨i, hi⟩ := (Multicover.covers_one_iff B t).mp h.2 T hT
      exact ⟨Sum.inl i, hi⟩
  have hn : Fintype.card (I ⊕ Fin (b - Fintype.card I)) = b := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let e := (Fintype.equivFinOfCardEq hn).symm
  exact ⟨C ∘ e, (Multicover.isCover_reindex e C k t 1).mpr hc⟩

/-- An exclusion at one fixed budget excludes every smaller budget. -/
theorem lower_of_fixed_exclusion {V : Type u} {I : Type v}
    [Fintype V] [DecidableEq V] [Fintype I] {B : I → Finset V} {k t b : ℕ}
    (ht : t ≤ Fintype.card V) (h : Multicover.IsCover B k t 1)
    (hex : ∀ D : Fin b → Finset V, ¬ Multicover.IsCover D k t 1) :
    b + 1 ≤ Fintype.card I := by
  by_contra hn
  obtain ⟨D, hD⟩ := pad ht h (show Fintype.card I ≤ b by omega)
  exact hex D hD

#guard_standard_axioms nonempty_occurrences pad lower_of_fixed_exclusion

end CoveringDesigns.IndexedPadding
