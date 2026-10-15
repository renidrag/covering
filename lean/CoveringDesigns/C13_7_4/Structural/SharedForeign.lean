import CoveringDesigns.C13_7_4.Structural.RootedCoreHelpers
import CoveringDesigns.C13_7_4.Structural.PrivateAlignment

/-!
A common overlap of size at least eight contains a foreign completed row in
both rooted descriptions. Core recognition rules out a full-row preimage;
the three intrinsic companions rule out an own-spine preimage.
-/

namespace CoveringDesigns.C13Structural

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

private theorem foreign_not_common :
    ∀ b u, insert u (transverse b) ∉ commonTraceFamily := by decide +kernel

private theorem foreign_not_contains_companions :
    ∀ b u, ¬ companions ⊆ insert u (transverse b) := by decide +kernel

private theorem common_not_contains_companions :
    ∀ i : Fin 3 × Bool, ¬ companions ⊆ commonTrace i.1 i.2 := by decide +kernel

namespace OrdinaryRootedFrame

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
    {C : Family α} {D : Family β} {p : α} {q : β}

/-- The own completed trace is the unique overlap row containing all
three intrinsic companion points. -/
theorem overlap_trace_eq_own_of_companions_subset
    (F : OrdinaryRootedFrame C p) {S : Finset TracePoint}
    (hS : S ∈ F.overlapTraces) (hA : companions ⊆ S) :
    S = (F.completed 0).eraseNone := by
  rw [F.overlapTraces_eq] at hS
  rcases mem_union.mp hS with hC | hshort
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hC
    exact False.elim (common_not_contains_companions i hA)
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hshort
    have hi012 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi012 with rfl | rfl | rfl
    · rfl
    · obtain ⟨u, _, he⟩ := F.foreign_trace_shape false hi
      exact False.elim (foreign_not_contains_companions false u (he ▸ hA))
    · obtain ⟨u, _, he⟩ := F.foreign_trace_shape true hi
      exact False.elim (foreign_not_contains_companions true u (he ▸ hA))

/-- The own completion, and hence its two additions, agree in both rooted
coordinate systems. -/
theorem own_trace_map_of_overlap_transport
    (F : OrdinaryRootedFrame C p) (G : OrdinaryRootedFrame D q)
    (e : Equiv.Perm TracePoint)
    (hcore : relabel e commonTraceFamily = commonTraceFamily)
    (hmem : ∀ S : Finset TracePoint,
      S.map e.toEmbedding ∈ F.overlapTraces ↔ S ∈ G.overlapTraces) :
    ((G.completed 0).eraseNone).map e.toEmbedding = (F.completed 0).eraseNone := by
  have hG : (G.completed 0).eraseNone ∈ G.overlapTraces := by
    rw [G.overlapTraces_eq]
    exact mem_union_right _ (mem_image.mpr ⟨0, G.own_selected, rfl⟩)
  apply F.overlap_trace_eq_own_of_companions_subset ((hmem _).mpr hG)
  have hs : companions.map e.toEmbedding ⊆ ((G.completed 0).eraseNone).map e.toEmbedding :=
    map_subset_map.mpr G.companions_subset_own_trace
  simpa only [core_preserving_map_companions e hcore] using hs

/-- A completed foreign row is common in the two rooted coordinate systems. -/
theorem shared_foreign_of_overlap_transport
    (F : OrdinaryRootedFrame C p) (G : OrdinaryRootedFrame D q)
    (e : Equiv.Perm TracePoint)
    (hcore : relabel e commonTraceFamily = commonTraceFamily)
    (hmem : ∀ S : Finset TracePoint,
      S.map e.toEmbedding ∈ F.overlapTraces ↔ S ∈ G.overlapTraces)
    (hdeg : 8 ≤ degree C p) :
    ∃ (b c : Bool) (u v : TracePoint),
      foreignIndex b ∈ F.selectedSpines ∧ foreignIndex c ∈ G.selectedSpines ∧
      u ∉ transverse b ∧ v ∉ transverse c ∧
      (F.completed (foreignIndex b)).eraseNone = insert u (transverse b) ∧
      (G.completed (foreignIndex c)).eraseNone = insert v (transverse c) ∧
      (insert v (transverse c)).map e.toEmbedding = insert u (transverse b) := by
  obtain ⟨b, hb⟩ := F.exists_foreign_selected hdeg
  obtain ⟨u, hu, hshapeF⟩ := F.foreign_trace_shape b hb
  have hT : insert u (transverse b) ∈ F.overlapTraces := by
    rw [F.overlapTraces_eq]
    exact mem_union_right _ (mem_image.mpr ⟨foreignIndex b, hb, hshapeF⟩)
  let S := (insert u (transverse b)).map e.symm.toEmbedding
  have hSe : S.map e.toEmbedding = insert u (transverse b) := by
    ext x
    simp [S]
  have hS : S ∈ G.overlapTraces := (hmem S).mp (hSe.symm ▸ hT)
  rw [G.overlapTraces_eq] at hS
  rcases mem_union.mp hS with hSC | hSshort
  · have heS : S.map e.toEmbedding ∈ relabel e commonTraceFamily :=
      (mem_relabel _ _ _).mpr hSC
    rw [hcore, hSe] at heS
    exact False.elim (foreign_not_common b u heS)
  · obtain ⟨i, hi, hiS⟩ := mem_image.mp hSshort
    have hi0 : i ≠ 0 := by
      intro he
      subst i
      have hAS : companions ⊆ S := hiS ▸ G.companions_subset_own_trace
      have hmap : companions.map e.toEmbedding ⊆ S.map e.toEmbedding :=
        map_subset_map.mpr hAS
      rw [core_preserving_map_companions e hcore, hSe] at hmap
      exact foreign_not_contains_companions b u hmap
    have hc : ∃ c : Bool, foreignIndex c = i := by
      have hi12 : i = 1 ∨ i = 2 := by omega
      rcases hi12 with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    obtain ⟨c, rfl⟩ := hc
    obtain ⟨v, hv, hshapeG⟩ := G.foreign_trace_shape c hi
    refine ⟨b, c, u, v, hb, hi, hu, hv, hshapeF, hshapeG, ?_⟩
    rw [← hshapeG, hiS, hSe]

end OrdinaryRootedFrame

#guard_standard_axioms OrdinaryRootedFrame.overlap_trace_eq_own_of_companions_subset
  OrdinaryRootedFrame.own_trace_map_of_overlap_transport
  OrdinaryRootedFrame.shared_foreign_of_overlap_transport

end CoveringDesigns.C13Structural
