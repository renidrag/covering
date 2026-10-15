import CoveringDesigns.C13_7_4.Structural.CoreAutomorphisms
import CoveringDesigns.C13_7_4.Structural.PrivateReconstruction

/-!
Once a common core and one foreign completed row agree, the private cores
are identical or differ by one spouse transposition.  The proof reconstructs
private rows functorially and never enumerates core automorphisms.
-/

namespace CoveringDesigns.C13Structural

open Finset

/-- Either named foreign half determines the complete private family. -/
theorem private_family_of_core_preserving_half
    (e : Equiv.Perm TracePoint)
    (he : relabel e commonTraceFamily = commonTraceFamily) (b : Bool) :
    relabel e privateTraceFamily =
      reconstructedPrivate commonTraceFamily companions ((transverse b).map e.toEmbedding) := by
  calc
    relabel e privateTraceFamily =
        relabel e (reconstructedPrivate commonTraceFamily companions (transverse b)) := by
      rw [reconstructedPrivate_common_transverse]
    _ = _ := by
      rw [relabel_reconstructedPrivate, he, core_preserving_map_companions e he]

/-- The gluing dichotomy retains the two extra points: in the nontrivial
case, one is carried to the spouse of the other. -/
theorem private_alignment_of_shared_foreign
    (e : Equiv.Perm TracePoint)
    (he : relabel e commonTraceFamily = commonTraceFamily)
    (b c : Bool) (u v : TracePoint)
    (hu : u ∉ transverse b) (hv : v ∉ transverse c)
    (hrow : (insert v (transverse c)).map e.toEmbedding = insert u (transverse b)) :
    relabel e privateTraceFamily = privateTraceFamily ∨
      (u ∈ spouseGround ∧ e v = spouseMate u ∧
        relabel e privateTraceFamily =
          relabel (Equiv.swap u (spouseMate u)) privateTraceFamily) := by
  rcases core_preserving_shared_foreign e he b c u v hu hv hrow with hhalf | hhalf
  · left
    rw [private_family_of_core_preserving_half e he c, hhalf,
      reconstructedPrivate_common_transverse]
  · right
    refine ⟨hhalf.1, hhalf.2.1, ?_⟩
    have hmate : spouseMate u ∈ transverse b := (canonical_transverse b).2 u hhalf.1 |>.mpr hu
    have hswap : (transverse b).map (Equiv.swap u (spouseMate u)).toEmbedding =
        insert u ((transverse b).erase (spouseMate u)) := map_swap_of_not_mem_mem hu hmate
    rw [private_family_of_core_preserving_half e he c,
      private_family_of_core_preserving_half _ (spouse_swap_preserves_core u) b,
      hhalf.2.2, hswap]

#guard_standard_axioms private_family_of_core_preserving_half
  private_alignment_of_shared_foreign

end CoveringDesigns.C13Structural
