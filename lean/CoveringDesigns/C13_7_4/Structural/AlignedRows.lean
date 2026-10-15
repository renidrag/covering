import CoveringDesigns.C13_7_4.Structural.OverlapAlignment
import CoveringDesigns.C13_7_4.Structural.PairNormalization
import CoveringDesigns.C13_7_4.Structural.HighPairs
import Mathlib.Data.Finset.Sum

/-! Actual forced global rows after normalizing one spouse swap.
The two additions of the own completed row remain arbitrary. -/

namespace CoveringDesigns.C13Structural
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- Add one named root to a six-point private trace. -/
def rootTraceBlock (r : Bool) (S : Finset TracePoint) : Finset SwapPoint :=
  insert (swapRoot r) (S.image Sum.inr)

theorem rootTraceBlock_normalization (v : Fin 4) (b r : Bool) (S : Finset TracePoint) :
    (rootTraceBlock r S).map (pairNormalization v b).toEmbedding =
      rootTraceBlock r (S.map (traceNormalization v b).toEmbedding) := by
  simp only [rootTraceBlock, map_insert, Equiv.coe_toEmbedding, pairNormalization_root]
  apply congrArg (insert (swapRoot r))
  simp only [map_eq_image, image_image, Function.comp_def, Equiv.coe_toEmbedding,
    pairNormalization_trace, traceNormalization_apply]

theorem addBothRoots_normalization (v : Fin 4) (b : Bool) (S : Finset TracePoint) :
    (addBothRoots S).map (pairNormalization v b).toEmbedding =
      addBothRoots (S.map (traceNormalization v b).toEmbedding) := by
  change (insert (swapRoot false) (insert (swapRoot true) (S.image Sum.inr))).map
    (pairNormalization v b).toEmbedding = _
  simp only [map_insert, Equiv.coe_toEmbedding, pairNormalization_root]
  apply congrArg (insert (swapRoot false))
  apply congrArg (insert (swapRoot true))
  simp only [map_eq_image, image_image, Function.comp_def, Equiv.coe_toEmbedding,
    pairNormalization_trace, traceNormalization_apply]

theorem normalization_swapped_trace (v : Fin 4) (b : Bool) (S : Finset TracePoint) :
    (S.image swapTrace).map (traceNormalization v b).toEmbedding =
      (S.map (traceNormalization v b).toEmbedding).map
        (Equiv.swap (Sum.inr (v, !b)) (Sum.inr (v, b))).toEmbedding := by
  simp only [map_eq_image, image_image, Function.comp_def, Equiv.coe_toEmbedding,
    traceNormalization_apply, normalization_conjugates_swap]

/-- Record arbitrary outside additions in the normalized spouse coordinates. -/
def normalizedAdditions (v : Fin 4) (b : Bool) (A : Finset TracePoint) :
    Finset (Fin 4 × Bool) :=
  (A.map (traceNormalization v b).toEmbedding).toRight

private theorem outside_toRight_image (A : Finset TracePoint)
    (hA : A ⊆ univ \ companions) : A.toRight.image Sum.inr = A := by
  ext x
  rcases x with m | z
  · constructor
    · intro h
      obtain ⟨y, _, he⟩ := mem_image.mp h
      cases he
    · intro h
      have hn := (mem_sdiff.mp (hA h)).2
      exact False.elim (hn (mem_image.mpr ⟨m, mem_univ _, rfl⟩))
  · simp

theorem normalizedAdditions_image (v : Fin 4) (b : Bool) (A : Finset TracePoint)
    (hA : A ⊆ univ \ companions) :
    (normalizedAdditions v b A).image Sum.inr = A.map (traceNormalization v b).toEmbedding := by
  apply outside_toRight_image
  have h := (map_subset_map (f := (traceNormalization v b).toEmbedding)).mpr hA
  simpa only [map_sdiff, map_univ_equiv, normalization_companions] using h

theorem normalizedAdditions_card (v : Fin 4) (b : Bool) (A : Finset TracePoint)
    (hA : A ⊆ univ \ companions) : (normalizedAdditions v b A).card = A.card := by
  have h := congrArg Finset.card (normalizedAdditions_image v b A hA)
  rw [card_image_of_injective _ Sum.inr_injective, card_map] at h
  exact h

theorem normalizedAdditions_map_back (v : Fin 4) (b : Bool) (A : Finset TracePoint)
    (hA : A ⊆ univ \ companions) :
    ((normalizedAdditions v b A).image Sum.inr).map (traceNormalization v b).toEmbedding = A := by
  rw [normalizedAdditions_image v b A hA]
  let n := traceNormalization v b
  have h : (A.map n.toEmbedding).map n.symm.toEmbedding = A := by
    ext x
    simp only [mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
  simpa only [n, traceNormalization_symm] using h

/-- Membership in normalized additions is the original membership transported
by the involutive coordinate change. -/
theorem mem_normalizedAdditions_iff (v : Fin 4) (b : Bool) (A : Finset TracePoint)
    (z : Fin 4 × Bool) :
    z ∈ normalizedAdditions v b A ↔ traceNormalization v b (Sum.inr z) ∈ A := by
  simp only [normalizedAdditions, mem_toRight, mem_map_equiv, traceNormalization_symm]

/-- The normalized y-points lie in the transverse half opposite the shared foreign row. -/
theorem normalization_other_half (v : Fin 4) (b : Bool) (w : Fin 4) :
    traceNormalization v b (Sum.inr (w, true)) ∈ transverse (!b) := by
  change Sum.inr (indexTranslate v w, Bool.xor b true) ∈ transverse (!b)
  have hb : Bool.xor b true = !b := by cases b <;> rfl
  rw [hb]
  exact mem_image.mpr ⟨indexTranslate v w, mem_univ _, rfl⟩

theorem normalization_other_ne_extra (v : Fin 4) (b : Bool) (w : Fin 4) (hw : w ≠ 0) :
    traceNormalization v b (Sum.inr (w, true)) ≠ Sum.inr (v, !b) := by
  intro h
  have he : traceNormalization v b (Sum.inr (w, true)) =
      traceNormalization v b (Sum.inr (0, true)) := h.trans (normalization_zero_mate v b).symm
  have hz := (traceNormalization v b).injective he
  exact hw (congrArg Prod.fst (Sum.inr.inj hz))

/-- An outside extra point belongs to the opposite member of its spouse pair. -/
theorem exists_spouse_opposite_half (b : Bool) (u : TracePoint)
    (hu : u ∈ spouseGround) (hhalf : u ∉ transverse b) :
    ∃ v : Fin 4, u = Sum.inr (v, !b) := by
  rcases u with m | ⟨v, c⟩
  · have hn := (mem_sdiff.mp hu).2
    exact False.elim (hn (mem_image.mpr ⟨m, mem_univ _, rfl⟩))
  · have hcb : c ≠ b := by
      intro he
      apply hhalf
      exact mem_image.mpr ⟨v, mem_univ _, by rw [he]⟩
    have hc : c = !b := by cases b <;> cases c <;> simp_all
    exact ⟨v, by rw [hc]⟩

section Actual
variable {α : Type*} [DecidableEq α] {C : Family α}
  {p q : α} {hpq : p ≠ q}
variable (F : OrdinaryRootedFrame (link C p) ⟨q, hpq.symm⟩)
variable (G : OrdinaryRootedFrame (link C q) ⟨p, hpq⟩)

private theorem first_private_mem {S : Finset TracePoint} (hS : S ∈ privateTraceFamily) :
    (rootTraceBlock false S).map F.globalLabel.toEmbedding ∈ C := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hS
  exact F.global_private_mem i.1 i.2

private theorem first_common_mem {S : Finset TracePoint} (hS : S ∈ commonTraceFamily) :
    (addBothRoots S).map F.globalLabel.toEmbedding ∈ C := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hS
  exact F.global_common_mem i.1 i.2

/-- The identical-core alternative yields the actual twelve private rows. -/
theorem identical_rows_of_private_alignment
    (hprivate : relabel (traceTransition F G) privateTraceFamily = privateTraceFamily) :
    ∀ i b, (identicalPrivateBlock i b).map F.globalLabel.toEmbedding ∈ C := by
  intro i b
  cases b with
  | false => exact F.global_private_mem i.1 i.2
  | true =>
      apply traceTransition_private_mem F G
      rw [hprivate]
      exact mem_image.mpr ⟨i, mem_univ _, rfl⟩

/-- Normalize an arbitrary spouse swap into the fixed displayed twelve rows. -/
theorem swapped_rows_of_private_alignment (v : Fin 4) (b : Bool)
    (hprivate : relabel (traceTransition F G) privateTraceFamily =
      relabel (Equiv.swap (Sum.inr (v, !b)) (Sum.inr (v, b))) privateTraceFamily) :
    HasSwappedPrivateRows C ((pairNormalization v b).trans F.globalLabel).toEmbedding := by
  intro i r
  have hS : (privateTrace i.1 i.2).map (traceNormalization v b).toEmbedding ∈
      privateTraceFamily := by
    rw [← normalization_private v b]
    exact (mem_relabel _ _ _).mpr (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  cases r with
  | false =>
      change (rootTraceBlock false (privateTrace i.1 i.2)).map
        ((pairNormalization v b).toEmbedding.trans F.globalLabel.toEmbedding) ∈ C
      rw [← map_map, rootTraceBlock_normalization]
      exact first_private_mem (hpq := hpq) F hS
  | true =>
      have hirow : swappedPrivateBlock i true =
          rootTraceBlock true ((privateTrace i.1 i.2).image swapTrace) := by
        simp only [swappedPrivateBlock, rootTraceBlock, ↓reduceIte,
          image_image, Function.comp_def]
      rw [hirow]
      change (rootTraceBlock true ((privateTrace i.1 i.2).image swapTrace)).map
        ((pairNormalization v b).toEmbedding.trans F.globalLabel.toEmbedding) ∈ C
      rw [← map_map, rootTraceBlock_normalization]
      apply traceTransition_private_mem F G
      rw [hprivate, normalization_swapped_trace]
      exact (mem_relabel _ _ _).mpr hS

/-- The common full rows are unchanged as a family by the normalization. -/
theorem normalized_common_rows (v : Fin 4) (b : Bool) :
    ∀ i, (swappedCommonBlock i).map
      ((pairNormalization v b).trans F.globalLabel).toEmbedding ∈ C := by
  intro i
  change (addBothRoots (commonTrace i.1 i.2)).map
    ((pairNormalization v b).toEmbedding.trans F.globalLabel.toEmbedding) ∈ C
  rw [← map_map, addBothRoots_normalization]
  apply first_common_mem (hpq := hpq) F
  rw [← normalization_common v b]
  exact (mem_relabel _ _ _).mpr (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

/-- The arbitrary own-spine additions are carried along by the same change
of coordinates as the full rows. -/
theorem normalized_own_row (v : Fin 4) (b : Bool) (A : Finset TracePoint)
    (hA : A ⊆ univ \ companions)
    (hown : (F.completed 0).eraseNone = companions ∪ A) :
    (swappedOwnBlock ((normalizedAdditions v b A).image Sum.inr)).map
      ((pairNormalization v b).trans F.globalLabel).toEmbedding ∈ C := by
  change (addBothRoots (companions ∪ (normalizedAdditions v b A).image Sum.inr)).map
    ((pairNormalization v b).toEmbedding.trans F.globalLabel.toEmbedding) ∈ C
  rw [← map_map, addBothRoots_normalization, map_union, normalization_companions,
    normalizedAdditions_map_back v b A hA]
  apply (F.overlap_mem_iff _).mp
  rw [← hown, F.overlapTraces_eq]
  exact mem_union_right _ (mem_image.mpr ⟨0, F.own_selected, rfl⟩)

/-- All rows required by the structural swap obstruction occur in the actual covering. -/
theorem aligned_swap_rows (v : Fin 4) (b : Bool) (A : Finset TracePoint)
    (hA : A ⊆ univ \ companions) (hcard : A.card = 2)
    (hown : (F.completed 0).eraseNone = companions ∪ A)
    (hprivate : relabel (traceTransition F G) privateTraceFamily =
      relabel (Equiv.swap (Sum.inr (v, !b)) (Sum.inr (v, b))) privateTraceFamily) :
    AlignedSwapRows C ((pairNormalization v b).trans F.globalLabel)
      (normalizedAdditions v b A) :=
  ⟨swapped_rows_of_private_alignment F G v b hprivate, normalized_common_rows (hpq := hpq) F v b,
    normalized_own_row (hpq := hpq) F v b A hA hown, (normalizedAdditions_card v b A hA).trans hcard⟩

/-- The shared foreign completion becomes the displayed five-point foreign trace. -/
theorem normalized_foreign_row (v : Fin 4) (b : Bool)
    (hb : foreignIndex b ∈ F.selectedSpines)
    (hforeign : (F.completed (foreignIndex b)).eraseNone =
      insert (Sum.inr (v, !b)) (transverse b)) :
    swappedForeignBlock.map ((pairNormalization v b).trans F.globalLabel).toEmbedding ∈ C := by
  change swappedForeignBlock.map
    ((pairNormalization v b).toEmbedding.trans F.globalLabel.toEmbedding) ∈ C
  rw [← map_map, normalization_foreign]
  apply (F.overlap_mem_iff _).mp
  rw [F.overlapTraces_eq]
  exact mem_union_right _ (mem_image.mpr ⟨foreignIndex b, hb, hforeign⟩)

end Actual

#guard_standard_axioms rootTraceBlock_normalization addBothRoots_normalization
  normalizedAdditions_image normalizedAdditions_card normalizedAdditions_map_back
  mem_normalizedAdditions_iff normalization_other_half normalization_other_ne_extra
  exists_spouse_opposite_half
  identical_rows_of_private_alignment swapped_rows_of_private_alignment
  normalized_common_rows normalized_own_row aligned_swap_rows normalized_foreign_row

end CoveringDesigns.C13Structural
