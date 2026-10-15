import CoveringDesigns.C13_7_4.Structural.RootedCoreHelpers
import Mathlib.Logic.Equiv.Option

/-! Extract common-root configurations from actual point links. These
coordinate changes preserve every block and retain all arbitrary additions. -/

namespace CoveringDesigns.C13Structural
open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- Coordinates for the deleted root, the retained root, and eleven traces. -/
abbrev TwoRootPoint := Bool ⊕ TracePoint

def twoRootOption : TwoRootPoint ≃ Option RootedPoint where
  toFun
    | Sum.inl false => none
    | Sum.inl true => some none
    | Sum.inr x => some (some x)
  invFun
    | none => Sum.inl false
    | some none => Sum.inl true
    | some (some x) => Sum.inr x
  left_inv x := by rcases x with (_ | _) | x <;> rfl
  right_inv x := by rcases x with _ | (_ | x) <;> rfl

def includeLocal : RootedPoint → TwoRootPoint
  | none => Sum.inl true
  | some x => Sum.inr x

def addDeletedRoot (B : Finset RootedPoint) : Finset TwoRootPoint :=
  insert (Sum.inl false) (B.image includeLocal)

def addBothRoots (S : Finset TracePoint) : Finset TwoRootPoint :=
  insert (Sum.inl false) (insert (Sum.inl true) (S.image Sum.inr))

theorem addDeletedRoot_incident (S : Finset TracePoint) :
    addDeletedRoot (insert none (liftTrace S)) = addBothRoots S := by
  simp only [addDeletedRoot, liftTrace, image_insert, image_image, addBothRoots,
    includeLocal, Function.comp_def]

theorem addDeletedRoot_private (S : Finset TracePoint) :
    addDeletedRoot (liftTrace S) = insert (Sum.inl false) (S.image Sum.inr) := by
  simp only [addDeletedRoot, liftTrace, image_image, includeLocal, Function.comp_def]

section Links
variable {α : Type*} [DecidableEq α] {C : Family α} {p : α}

/-- The defining deletion map has this exact inverse on blocks through p. -/
theorem mem_link_iff_insert (B : Finset {x : α // x ≠ p}) :
    B ∈ link C p ↔ insert p (B.map (Function.Embedding.subtype _)) ∈ C := by
  constructor
  · intro hB
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hB
    obtain ⟨hA, hpA⟩ := mem_filter.mp hA
    rw [subtype_map]
    have he : insert p (A.filter (· ≠ p)) = A := by
      ext x
      by_cases hx : x = p <;> simp [hx, hpA]
    rwa [he]
  · intro hB
    apply mem_image.mpr
    refine ⟨insert p (B.map (Function.Embedding.subtype _)),
      mem_filter.mpr ⟨hB, mem_insert_self _ _⟩, ?_⟩
    ext x
    simp only [mem_subtype, mem_insert, mem_map]
    constructor
    · rintro (hp | ⟨y, hy, he⟩)
      · exact (x.property hp).elim
      · have hxy : y = x := Subtype.ext he
        exact hxy ▸ hy
    · intro hx
      exact Or.inr ⟨x, hx, rfl⟩

namespace OrdinaryRootedFrame
variable {q : {x : α // x ≠ p}} (F : OrdinaryRootedFrame (link C p) q)

/-- Put the deleted root back, obtaining actual global coordinates. -/
def globalLabel : TwoRootPoint ≃ α :=
  twoRootOption.trans ((Equiv.optionCongr F.label).trans (Equiv.optionSubtypeNe p))

@[simp] theorem globalLabel_false : F.globalLabel (Sum.inl false) = p := rfl

@[simp] theorem globalLabel_true : F.globalLabel (Sum.inl true) = q.val := by
  change (F.label none).val = q.val
  exact congrArg Subtype.val F.root_eq

@[simp] theorem globalLabel_trace (x : TracePoint) :
    F.globalLabel (Sum.inr x) = (F.label (some x)).val := rfl

@[simp] theorem globalLabel_include (x : RootedPoint) :
    F.globalLabel (includeLocal x) = (F.label x).val := by cases x <;> rfl

theorem addDeletedRoot_map (B : Finset RootedPoint) :
    (addDeletedRoot B).map F.globalLabel.toEmbedding =
      insert p ((B.map F.label.toEmbedding).map (Function.Embedding.subtype _)) := by
  rw [addDeletedRoot, map_insert]
  simp only [Equiv.coe_toEmbedding, F.globalLabel_false]
  apply congrArg (insert p)
  simp only [map_eq_image, image_image, Function.comp_def,
    Equiv.coe_toEmbedding, Function.Embedding.coe_subtype, F.globalLabel_include]

theorem raw_mem_iff (B : Finset RootedPoint) :
    B ∈ F.rawFamily ↔ B.map F.label.toEmbedding ∈ link C p := by
  have h := mem_relabel F.label F.rawFamily B
  change B.map F.label.toEmbedding ∈
    relabel F.label (rootedCore ∪ univ.image F.completed) ↔ B ∈ F.rawFamily at h
  rw [F.family_eq] at h
  exact h.symm

theorem global_mem_iff (B : Finset RootedPoint) :
    (addDeletedRoot B).map F.globalLabel.toEmbedding ∈ C ↔ B ∈ F.rawFamily := by
  rw [F.addDeletedRoot_map, ← mem_link_iff_insert, F.raw_mem_iff]

/-- The entire actual common overlap, in the first rooted frame. -/
theorem overlap_mem_iff (S : Finset TracePoint) :
    S ∈ F.overlapTraces ↔ (addBothRoots S).map F.globalLabel.toEmbedding ∈ C := by
  rw [F.mem_overlapTraces_iff, ← addDeletedRoot_incident, F.global_mem_iff]

theorem global_common_mem (m : Fin 3) (b : Bool) :
    (addBothRoots (commonTrace m b)).map F.globalLabel.toEmbedding ∈ C := by
  rw [← addDeletedRoot_incident, F.global_mem_iff]
  apply mem_union_left
  apply mem_union_left
  apply mem_image.mpr
  refine ⟨commonTrace m b, ?_, rfl⟩
  exact mem_image.mpr ⟨(m, b), mem_univ _, rfl⟩

theorem global_private_mem (m : Fin 3) (b : Bool) :
    (insert (Sum.inl false) ((privateTrace m b).image Sum.inr)).map
      F.globalLabel.toEmbedding ∈ C := by
  rw [← addDeletedRoot_private, F.global_mem_iff]
  apply mem_union_left
  apply mem_union_right
  apply mem_image.mpr
  refine ⟨privateTrace m b, ?_, rfl⟩
  exact mem_image.mpr ⟨(m, b), mem_univ _, rfl⟩

theorem global_completed_mem (i : Fin 3) :
    (addDeletedRoot (F.completed i)).map F.globalLabel.toEmbedding ∈ C := by
  rw [F.global_mem_iff]
  exact mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

end OrdinaryRootedFrame
end Links

#guard_standard_axioms mem_link_iff_insert OrdinaryRootedFrame.overlap_mem_iff
  OrdinaryRootedFrame.global_common_mem OrdinaryRootedFrame.global_private_mem

end CoveringDesigns.C13Structural
