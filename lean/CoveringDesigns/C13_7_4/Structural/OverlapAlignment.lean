import CoveringDesigns.C13_7_4.Structural.OverlapFrames
import CoveringDesigns.C13_7_4.Structural.CoreRecognition

/-! The two rooted descriptions of an actual common overlap have an exact
trace transition. Core recognition therefore aligns their six full rows. -/

namespace CoveringDesigns.C13Structural
open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

section Generic
variable {α : Type*} [DecidableEq α] {C : Family α}

namespace OrdinaryRootedFrame
variable {p : α} {q : {x : α // x ≠ p}} (F : OrdinaryRootedFrame (link C p) q)

private def tracePoint (x : TracePoint) : {y : α // y ≠ p ∧ y ≠ q.val} :=
  ⟨(F.label (some x)).val, (F.label (some x)).property, by
    intro hx
    have hq : F.label (some x) = q := Subtype.ext hx
    have he := F.label.injective (hq.trans F.root_eq.symm)
    cases he⟩

/-- Coordinates for the actual eleven points outside the two roots. -/
noncomputable def traceLabel : TracePoint ≃ {y : α // y ≠ p ∧ y ≠ q.val} :=
  Equiv.ofBijective F.tracePoint ⟨by
    intro x y hxy
    apply Option.some.inj
    apply F.label.injective
    apply Subtype.ext
    exact congrArg (fun z : {y : α // y ≠ p ∧ y ≠ q.val} => z.val) hxy,
  by
    intro x
    obtain ⟨r, hr⟩ := F.label.surjective ⟨x.val, x.property.1⟩
    cases r with
    | none =>
        have hq : q.val = x.val := congrArg Subtype.val (F.root_eq.symm.trans hr)
        exact False.elim (x.property.2 hq.symm)
    | some z =>
        refine ⟨z, ?_⟩
        apply Subtype.ext
        change (F.label (some z)).val = x.val
        exact congrArg (fun y : {y : α // y ≠ p} => y.val) hr⟩

@[simp] theorem traceLabel_val (x : TracePoint) :
    (F.traceLabel x).val = F.globalLabel (Sum.inr x) := rfl

end OrdinaryRootedFrame

private def outsidePairSwap (p q : α) :
    {x : α // x ≠ p ∧ x ≠ q} ≃ {x : α // x ≠ q ∧ x ≠ p} where
  toFun x := ⟨x.val, x.property.2, x.property.1⟩
  invFun x := ⟨x.val, x.property.2, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {p q : α} {hpq : p ≠ q}
variable (F : OrdinaryRootedFrame (link C p) ⟨q, hpq.symm⟩)
variable (G : OrdinaryRootedFrame (link C q) ⟨p, hpq⟩)

/-- Express the second frame's trace coordinates in the first frame. -/
noncomputable def traceTransition : Equiv.Perm TracePoint :=
  G.traceLabel.trans ((outsidePairSwap q p).trans F.traceLabel.symm)

theorem traceTransition_point (x : TracePoint) :
    F.globalLabel (Sum.inr (traceTransition F G x)) = G.globalLabel (Sum.inr x) := by
  change (F.traceLabel (traceTransition F G x)).val = (G.traceLabel x).val
  exact congrArg Subtype.val
    (F.traceLabel.apply_symm_apply (outsidePairSwap q p (G.traceLabel x)))

/-- Both descriptions of any common trace give the same actual global block. -/
theorem traceTransition_addBothRoots (S : Finset TracePoint) :
    (addBothRoots (S.map (traceTransition F G).toEmbedding)).map F.globalLabel.toEmbedding =
      (addBothRoots S).map G.globalLabel.toEmbedding := by
  simp only [addBothRoots, map_insert, Equiv.coe_toEmbedding,
    OrdinaryRootedFrame.globalLabel_false, OrdinaryRootedFrame.globalLabel_true]
  rw [insert_comm p q]
  apply congrArg (insert q)
  apply congrArg (insert p)
  simp only [map_eq_image, image_image, Function.comp_def, Equiv.coe_toEmbedding]
  apply image_congr
  intro x hx
  exact traceTransition_point F G x

/-- Membership in the overlap is independent of which minimum link describes it. -/
theorem traceTransition_mem_overlap (S : Finset TracePoint) :
    S.map (traceTransition F G).toEmbedding ∈ F.overlapTraces ↔ S ∈ G.overlapTraces := by
  rw [F.overlap_mem_iff, G.overlap_mem_iff, traceTransition_addBothRoots]

theorem traceTransition_core_subset :
    relabel (traceTransition F G) commonTraceFamily ⊆ F.overlapTraces := by
  intro B hB
  obtain ⟨S, hS, rfl⟩ := mem_map.mp hB
  apply (traceTransition_mem_overlap F G S).mpr
  rw [G.overlapTraces_eq]
  exact mem_union_left _ hS

/-- The six common full rows agree for actual overlapping ordinary links. -/
theorem traceTransition_preserves_core :
    relabel (traceTransition F G) commonTraceFamily = commonTraceFamily := by
  obtain ⟨S, u, v, _, hAS, hu, hv, hsub⟩ := F.overlap_shape
  apply sixCore_unique_in_overlap _ S u v
    (commonTraceFamily_isSixCore.relabel (traceTransition F G)) hAS hu hv
  exact (traceTransition_core_subset F G).trans hsub

/-- Private blocks of the second frame have the second root in the first
frame's global coordinates, with their trace transported by the same map. -/
theorem traceTransition_private_map (S : Finset TracePoint) :
    (insert (Sum.inl true)
      ((S.map (traceTransition F G).toEmbedding).image Sum.inr)).map
      F.globalLabel.toEmbedding =
    (insert (Sum.inl false) (S.image Sum.inr)).map G.globalLabel.toEmbedding := by
  simp only [map_insert, Equiv.coe_toEmbedding,
    OrdinaryRootedFrame.globalLabel_false, OrdinaryRootedFrame.globalLabel_true]
  apply congrArg (insert q)
  simp only [map_eq_image, image_image, Function.comp_def, Equiv.coe_toEmbedding]
  apply image_congr
  intro x hx
  exact traceTransition_point F G x

/-- Every private row in the relabelled second core is an actual block. -/
theorem traceTransition_private_mem {S : Finset TracePoint}
    (hS : S ∈ relabel (traceTransition F G) privateTraceFamily) :
    (insert (Sum.inl true) (S.image Sum.inr)).map F.globalLabel.toEmbedding ∈ C := by
  obtain ⟨T, hT, rfl⟩ := mem_map.mp hS
  obtain ⟨i, _, rfl⟩ := mem_image.mp hT
  change (insert (Sum.inl true)
    (((privateTrace i.1 i.2).map (traceTransition F G).toEmbedding).image Sum.inr)).map
      F.globalLabel.toEmbedding ∈ C
  rw [traceTransition_private_map]
  exact G.global_private_mem i.1 i.2

end Generic

#guard_standard_axioms traceTransition_point traceTransition_addBothRoots
  traceTransition_mem_overlap traceTransition_core_subset traceTransition_preserves_core
  traceTransition_private_map traceTransition_private_mem

end CoveringDesigns.C13Structural
