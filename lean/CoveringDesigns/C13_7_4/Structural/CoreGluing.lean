import CoveringDesigns.Foundations.Basic
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Logic.Equiv.Basic

/-!
A shared completed foreign spine fixes its transverse half, except for a
single spouse swap.  This set-theoretic argument works for both eight-row
and nine-row overlaps; it does not enumerate choices of added points.
-/

namespace CoveringDesigns.C13Structural

open Finset

variable {α : Type*} [DecidableEq α]

/-- A set contains exactly one member of each spouse pair in `X`. -/
def IsTransverse (X : Finset α) (mate : α → α) (B : Finset α) : Prop :=
  B ⊆ X ∧ ∀ x ∈ X, (mate x ∈ B ↔ x ∉ B)

/-- Two sets obtained by deleting one point from the same set differ by
exchanging precisely their omitted points. -/
theorem exchange_of_insert_eq {B B' : Finset α} {u v : α}
    (hv : v ∉ B') (he : insert u B = insert v B') (huv : u ≠ v) :
    v ∈ B ∧ u ∈ B' ∧ B' = insert u (B.erase v) := by
  have huB' : u ∈ B' := by
    have h : u ∈ insert v B' := he ▸ mem_insert_self u B
    exact (mem_insert.mp h).resolve_left huv
  have hvB : v ∈ B := by
    have h : v ∈ insert u B := he.symm ▸ mem_insert_self v B'
    exact (mem_insert.mp h).resolve_left (Ne.symm huv)
  refine ⟨hvB, huB', ?_⟩
  calc
    B' = (insert v B').erase v := by simp [hv]
    _ = (insert u B).erase v := congrArg (fun S => S.erase v) he.symm
    _ = insert u (B.erase v) := erase_insert_of_ne huv

/-- One five-point foreign row suffices to align two transverse four-point
halves.  If the omitted point changes, the exchange is a spouse swap.  No
assumption about the size of the ground set is needed. -/
theorem transverse_extension_unique_or_swap
    {X B B' : Finset α} {mate : α → α} {u v : α}
    (hB : IsTransverse X mate B) (hB' : IsTransverse X mate B')
    (hu : u ∉ B) (hv : v ∉ B') (he : insert u B = insert v B') :
    B' = B ∨ (u ∈ X ∧ v = mate u ∧ B' = insert u (B.erase (mate u))) := by
  by_cases huv : u = v
  · left
    subst v
    simpa [hu, hv] using (congrArg (fun S => S.erase u) he).symm
  · obtain ⟨hvB, huB', hswap⟩ := exchange_of_insert_eq hv he huv
    have huX := hB'.1 huB'
    have hmB : mate u ∈ B := (hB.2 u huX).mpr hu
    have hmB' : mate u ∉ B' := by
      intro hm
      exact ((hB'.2 u huX).mp hm) huB'
    have hvm : v = mate u := by
      by_contra hne
      apply hmB'
      rw [hswap]
      exact mem_insert_of_mem (mem_erase.mpr ⟨Ne.symm hne, hmB⟩)
    exact Or.inr ⟨huX, hvm, by simpa only [hvm] using hswap⟩

/-- Exchanging the unique omitted and inserted points is exactly the
point transposition on the transverse set. -/
theorem map_swap_of_not_mem_mem {B : Finset α} {u v : α}
    (hu : u ∉ B) (hv : v ∈ B) :
    B.map (Equiv.swap u v).toEmbedding = insert u (B.erase v) := by
  have huv : u ≠ v := by intro he; exact hu (he.symm ▸ hv)
  ext x
  by_cases hxu : x = u
  · subst x
    simp [hu, hv]
  by_cases hxv : x = v
  · subst x
    simp [hu, hv, Ne.symm huv]
  simp [Equiv.swap_apply_def, hxu, hxv]

#guard_standard_axioms exchange_of_insert_eq transverse_extension_unique_or_swap
  map_swap_of_not_mem_mem

end CoveringDesigns.C13Structural
