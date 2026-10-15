import CoveringDesigns.C13_7_4.Structural.RootedCore

/-!
The six private rows are determined by the common six-row core, its three
companions and one transverse half. This functorial formula avoids any
classification or enumeration of core automorphisms.
-/

namespace CoveringDesigns.C13Structural

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Reverse parity on one transverse half of the common row. -/
def privateFromCommon (A B S : Finset α) : Finset α :=
  (A \ S) ∪ (S ∩ B) ∪ ((univ \ A) \ (S ∪ B))

def reconstructedPrivate (Q : Family α) (A B : Finset α) : Family α :=
  Q.image (privateFromCommon A B)

/-- The reconstruction is independent of the names of points. -/
theorem map_privateFromCommon (e : α ≃ β) (A B S : Finset α) :
    (privateFromCommon A B S).map e.toEmbedding =
      privateFromCommon (A.map e.toEmbedding) (B.map e.toEmbedding) (S.map e.toEmbedding) := by
  simp only [privateFromCommon, map_union, map_sdiff, map_inter, map_univ_equiv]

theorem relabel_reconstructedPrivate (e : α ≃ β) (Q : Family α) (A B : Finset α) :
    relabel e (reconstructedPrivate Q A B) =
      reconstructedPrivate (relabel e Q) (A.map e.toEmbedding) (B.map e.toEmbedding) := by
  unfold reconstructedPrivate relabel
  rw [map_eq_image (Finset.mapEmbedding e.toEmbedding).toEmbedding
    (Q.image (privateFromCommon A B)), image_image,
    map_eq_image (Finset.mapEmbedding e.toEmbedding).toEmbedding Q, image_image]
  apply congrArg (fun f => Q.image f)
  funext S
  exact map_privateFromCommon e A B S

/-- Naming the other transverse half makes no difference to the private family. -/
theorem reconstructedPrivate_common_transverse : ∀ b,
    reconstructedPrivate commonTraceFamily companions (transverse b) = privateTraceFamily := by
  decide +kernel

#guard_standard_axioms map_privateFromCommon relabel_reconstructedPrivate
  reconstructedPrivate_common_transverse

end CoveringDesigns.C13Structural
