import CoveringDesigns.C13_7_4.Structural.RootedDegrees
import CoveringDesigns.C13_7_4.Structural.OverlapAlignment
import CoveringDesigns.C13_7_4.Structural.SharedForeign

/-!
A point avoiding two shared completed rows has degree seven in both ordinary
links. There are only three completed rows, so all remaining completion
additions are irrelevant. The argument treats overlaps of size eight and
nine uniformly.
-/

namespace CoveringDesigns.C13Structural

open Finset

variable {α : Type*} [DecidableEq α] {C : Family α}
    {p q : α} {hpq : p ≠ q}

/-- Two shared completed rows suffice for both minimum local degrees. -/
theorem pair_degrees_seven_avoids_shared
    (F : OrdinaryRootedFrame (link C p) ⟨q, hpq.symm⟩)
    (G : OrdinaryRootedFrame (link C q) ⟨p, hpq⟩)
    (b c : Bool)
    (hforeign : ((G.completed (foreignIndex c)).eraseNone).map
      (traceTransition F G).toEmbedding = (F.completed (foreignIndex b)).eraseNone)
    (x : TracePoint)
    (hxown : x ∉ (F.completed 0).eraseNone)
    (hxforeign : x ∉ (F.completed (foreignIndex b)).eraseNone) :
    degree (star C p) (F.globalLabel (Sum.inr x)) = 7 ∧
      degree (star C q) (F.globalLabel (Sum.inr x)) = 7 := by
  have hF : degree (star C p) (F.globalLabel (Sum.inr x)) = 7 := by
    simpa only [OrdinaryRootedFrame.globalLabel_trace, degree_link] using
      F.degree_seven_avoids_two_completed b hxown hxforeign
  have hown := F.own_trace_map_of_overlap_transport G (traceTransition F G)
    (traceTransition_preserves_core F G) (traceTransition_mem_overlap F G)
  let y := (traceTransition F G).symm x
  have hyown : y ∉ (G.completed 0).eraseNone := by
    simpa only [← hown, mem_map_equiv] using hxown
  have hyforeign : y ∉ (G.completed (foreignIndex c)).eraseNone := by
    simpa only [← hforeign, mem_map_equiv] using hxforeign
  have hG : degree (star C q) (G.globalLabel (Sum.inr y)) = 7 := by
    simpa only [OrdinaryRootedFrame.globalLabel_trace, degree_link] using
      G.degree_seven_avoids_two_completed c hyown hyforeign
  rw [← traceTransition_point F G y, (traceTransition F G).apply_symm_apply x] at hG
  exact ⟨hF, hG⟩

/-- The usual opposite-half condition implies avoidance of the two shared
rows. Neither root's degree is assumed to be eight rather than nine. -/
theorem pair_degrees_seven_of_shared_shapes
    (F : OrdinaryRootedFrame (link C p) ⟨q, hpq.symm⟩)
    (G : OrdinaryRootedFrame (link C q) ⟨p, hpq⟩)
    (b c : Bool) (R : Finset TracePoint) (u : TracePoint)
    (hown : (F.completed 0).eraseNone = companions ∪ R)
    (hshape : (F.completed (foreignIndex b)).eraseNone = insert u (transverse b))
    (hforeign : ((G.completed (foreignIndex c)).eraseNone).map
      (traceTransition F G).toEmbedding = (F.completed (foreignIndex b)).eraseNone)
    {x : TracePoint} (hx : x ∈ transverse (!b)) (hxR : x ∉ R) (hxu : x ≠ u) :
    degree (star C p) (F.globalLabel (Sum.inr x)) = 7 ∧
      degree (star C q) (F.globalLabel (Sum.inr x)) = 7 := by
  obtain ⟨v, _, rfl⟩ := mem_image.mp hx
  apply pair_degrees_seven_avoids_shared F G b c hforeign (Sum.inr (v, !b))
  · rw [hown, mem_union, not_or]
    exact ⟨by simp [companions], hxR⟩
  · rw [hshape, mem_insert, not_or]
    exact ⟨hxu, by cases b <;> simp [transverse]⟩

#guard_standard_axioms pair_degrees_seven_avoids_shared pair_degrees_seven_of_shared_shapes

end CoveringDesigns.C13Structural
