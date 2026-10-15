import CoveringDesigns.C13_7_4.Structural.OverlapFrames

/-! Avoiding two of the three completed spines leaves exactly one completed
incidence. Together with the six core incidences, this gives degree seven.
The argument does not depend on the root's multiplicity or on any additions. -/

namespace CoveringDesigns.C13Structural
open Finset

namespace OrdinaryRootedFrame
variable {α : Type*} [DecidableEq α] {C : Family α} {q : α}
variable (F : OrdinaryRootedFrame C q)

/-- Every point belongs to a spine completion. A point avoiding two of them
therefore belongs to exactly the third, and has degree seven. -/
theorem degree_seven_avoids_two_completed (b : Bool) {x : TracePoint}
    (hxown : x ∉ (F.completed 0).eraseNone)
    (hxforeign : x ∉ (F.completed (foreignIndex b)).eraseNone) :
    degree C (F.label (some x)) = 7 := by
  let hits := univ.filter (fun i => some x ∈ F.completed i)
  have hpos : 0 < hits.card := by
    obtain ⟨i, hi⟩ := rooted_spines_cover (some x)
    exact card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, F.spine_subset i hi⟩⟩
  have hsub : hits ⊆ univ \ {0, foreignIndex b} := by
    intro i hi
    have hmem := (mem_filter.mp hi).2
    apply mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hi
    rcases mem_insert.mp hi with rfl | hi
    · exact hxown (mem_eraseNone.mpr hmem)
    · have he := mem_singleton.mp hi
      exact hxforeign (mem_eraseNone.mpr (he ▸ hmem))
  have hcard : (univ \ ({0, foreignIndex b} : Finset (Fin 3))).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ _)]
    cases b <;> simp [foreignIndex]
  have hle := card_le_card hsub
  rw [hcard] at hle
  rw [F.degree_label]
  change 6 + hits.card = 7
  omega

end OrdinaryRootedFrame

#guard_standard_axioms OrdinaryRootedFrame.degree_seven_avoids_two_completed

end CoveringDesigns.C13Structural
