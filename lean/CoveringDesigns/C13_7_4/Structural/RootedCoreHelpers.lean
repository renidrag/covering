import CoveringDesigns.C13_7_4.Structural.RootedCore
import CoveringDesigns.C12_6_3.Structural.Separation
import Mathlib.Data.Finset.Option

/-! Symbolic descriptions of the completed rows through a chosen root.
All additions remain arbitrary throughout these counting arguments. -/

namespace CoveringDesigns.C13Structural
open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def foreignIndex (b : Bool) : Fin 3 := if b then 2 else 1

theorem foreign_spine_eq : ∀ b, rootedSpine (foreignIndex b) = liftTrace (transverse b) := by
  decide +kernel

theorem companions_card : companions.card = 3 := by decide +kernel

theorem transverse_card : ∀ b, (transverse b).card = 4 := by decide +kernel

theorem rooted_spines_union_card : ∀ i j, i ≠ j →
    (rootedSpine i ∪ rootedSpine j).card = 8 := by decide +kernel

theorem rooted_core_contains_no_spine : ∀ i, ∀ B ∈ rootedCore, ¬ rootedSpine i ⊆ B := by
  decide +kernel

/-- The three spines partition the rooted points; every point has a completed row. -/
theorem rooted_spines_cover (x : RootedPoint) : ∃ i, x ∈ rootedSpine i := by
  rcases x with _ | (m | ⟨v, b⟩)
  · exact ⟨0, by decide +kernel⟩
  · exact ⟨0, by simp [rootedSpine, liftTrace, companions]⟩
  · refine ⟨foreignIndex b, ?_⟩
    rw [foreign_spine_eq]
    simp [liftTrace, transverse]

/-- The full core contributes exactly six incidences at every point. -/
theorem rooted_core_degree (x : RootedPoint) : degree rootedCore x = 6 := by
  have h := degree_relabel rootedLabel rootedCore x
  rw [rootedCore_eq_figure1, GPPTStructural.core_degree] at h
  exact h.symm

namespace OrdinaryRootedFrame
variable {α : Type*} [DecidableEq α]
  {C : Family α} {q : α} (F : OrdinaryRootedFrame C q)

def rawFamily : Family RootedPoint := rootedCore ∪ univ.image F.completed

def selectedSpines : Finset (Fin 3) := univ.filter (fun i => none ∈ F.completed i)

def overlapTraces : Family TracePoint := (star F.rawFamily none).image eraseNone

theorem own_contains_root : none ∈ F.completed 0 :=
  F.spine_subset 0 (by decide +kernel)

theorem own_selected : (0 : Fin 3) ∈ F.selectedSpines := by
  exact mem_filter.mpr ⟨mem_univ _, F.own_contains_root⟩

theorem selected_iff (i : Fin 3) : i ∈ F.selectedSpines ↔ none ∈ F.completed i := by
  simp [selectedSpines]

theorem completed_injective : Function.Injective F.completed := by
  intro i j hij
  by_contra hn
  have hs : rootedSpine i ∪ rootedSpine j ⊆ F.completed j := by
    apply union_subset
    · exact hij ▸ F.spine_subset i
    · exact F.spine_subset j
  have hc := card_le_card hs
  rw [rooted_spines_union_card i j hn, F.completed_card] at hc
  omega

theorem core_disjoint_completed : Disjoint rootedCore (univ.image F.completed) := by
  apply disjoint_left.mpr
  intro B hB hBC
  obtain ⟨i, _, rfl⟩ := mem_image.mp hBC
  exact rooted_core_contains_no_spine i (F.completed i) hB (F.spine_subset i)

/-- Six full-core incidences plus the completed-spine incidences account for every degree. -/
theorem raw_degree_at (x : RootedPoint) :
    degree F.rawFamily x = 6 + (univ.filter fun i => x ∈ F.completed i).card := by
  have hd : Disjoint (rootedCore.filter (x ∈ ·))
      ((univ.image F.completed).filter (x ∈ ·)) :=
    F.core_disjoint_completed.mono (filter_subset _ _) (filter_subset _ _)
  change ((rootedCore ∪ univ.image F.completed).filter (x ∈ ·)).card = _
  rw [filter_union, card_union_of_disjoint hd]
  change degree rootedCore x + ((univ.image F.completed).filter (x ∈ ·)).card = _
  rw [rooted_core_degree, filter_image, card_image_of_injective _ F.completed_injective]

theorem degree_label (x : RootedPoint) :
    degree C (F.label x) = 6 + (univ.filter fun i => x ∈ F.completed i).card := by
  have h := degree_relabel F.label F.rawFamily x
  change degree (relabel F.label (rootedCore ∪ univ.image F.completed)) (F.label x) = _ at h
  rw [F.family_eq] at h
  exact h.trans (F.raw_degree_at x)

theorem root_degree : degree C q = 6 + F.selectedSpines.card := by
  simpa only [F.root_eq, selectedSpines] using F.degree_label none

theorem completed_trace_card {i : Fin 3} (hi : i ∈ F.selectedSpines) :
    (F.completed i).eraseNone.card = 5 := by
  rw [card_eraseNone_of_mem ((F.selected_iff i).mp hi), F.completed_card]

theorem companions_subset_own_trace : companions ⊆ (F.completed 0).eraseNone := by
  intro x hx
  apply mem_eraseNone.mpr
  apply F.spine_subset 0
  change some x ∈ insert none (liftTrace companions)
  exact mem_insert_of_mem (mem_image.mpr ⟨x, hx, rfl⟩)

/-- The own-spine overlap row contains exactly two arbitrary outside points. -/
theorem own_trace_shape : ∃ R : Finset TracePoint,
    R ⊆ univ \ companions ∧ R.card = 2 ∧
    (F.completed 0).eraseNone = companions ∪ R := by
  let S := (F.completed 0).eraseNone
  refine ⟨S \ companions, ?_, ?_, ?_⟩
  · intro x hx
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
  · rw [card_sdiff_of_subset F.companions_subset_own_trace,
      F.completed_trace_card F.own_selected, companions_card]
  · exact (union_sdiff_of_subset F.companions_subset_own_trace).symm

theorem transverse_subset_foreign_trace (b : Bool) :
    transverse b ⊆ (F.completed (foreignIndex b)).eraseNone := by
  intro x hx
  apply mem_eraseNone.mpr
  apply F.spine_subset (foreignIndex b)
  rw [foreign_spine_eq]
  exact mem_image.mpr ⟨x, hx, rfl⟩

/-- A foreign spine through the root has exactly one other added point. -/
theorem foreign_trace_shape (b : Bool) (hb : foreignIndex b ∈ F.selectedSpines) :
    ∃ u : TracePoint, u ∉ transverse b ∧
      (F.completed (foreignIndex b)).eraseNone = insert u (transverse b) := by
  let S := (F.completed (foreignIndex b)).eraseNone
  have hcard : (S \ transverse b).card = 1 := by
    rw [card_sdiff_of_subset (F.transverse_subset_foreign_trace b),
      F.completed_trace_card hb, transverse_card]
  obtain ⟨u, hu⟩ := card_eq_one.mp hcard
  have hum : u ∈ S \ transverse b := by rw [hu]; exact mem_singleton_self _
  refine ⟨u, (mem_sdiff.mp hum).2, ?_⟩
  have hh := union_sdiff_of_subset (F.transverse_subset_foreign_trace b)
  change transverse b ∪ (S \ transverse b) = S at hh
  rw [hu] at hh
  simpa only [union_singleton] using hh.symm

theorem overlapTraces_eq :
    F.overlapTraces = commonTraceFamily ∪
      F.selectedSpines.image (fun i => (F.completed i).eraseNone) := by
  have hi : (univ.image F.completed).filter (none ∈ ·) =
      F.selectedSpines.image F.completed := by
    simp only [selectedSpines, filter_image]
  have hcore : (star rootedCore none).image eraseNone = commonTraceFamily := by
    decide +kernel
  unfold overlapTraces rawFamily star
  rw [filter_union, image_union, hi, image_image]
  rw [show (rootedCore.filter (none ∈ ·)).image eraseNone = commonTraceFamily from hcore]
  rfl

/-- Degree at least eight ensures that a foreign completed spine contains the root. -/
theorem exists_foreign_selected (hdeg : 8 ≤ degree C q) :
    ∃ b, foreignIndex b ∈ F.selectedSpines := by
  have hn : 1 < F.selectedSpines.card := by have h := F.root_degree; omega
  obtain ⟨i, hi, hi0⟩ := exists_mem_ne hn 0
  have hi12 : i = 1 ∨ i = 2 := by omega
  rcases hi12 with rfl | rfl
  · exact ⟨false, hi⟩
  · exact ⟨true, hi⟩

/-- Deleting and reinserting a root records exactly the incident rows. -/
theorem mem_overlapTraces_iff (S : Finset TracePoint) :
    S ∈ F.overlapTraces ↔ insert none (liftTrace S) ∈ F.rawFamily := by
  constructor
  · intro hS
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hS
    obtain ⟨hB, hn⟩ := mem_filter.mp hB
    have he : insert none (liftTrace B.eraseNone) = B := by
      rw [liftTrace, image_some_eraseNone, insert_erase hn]
    exact he.symm ▸ hB
  · intro hS
    apply mem_image.mpr
    refine ⟨insert none (liftTrace S), mem_filter.mpr ⟨hS, mem_insert_self _ _⟩, ?_⟩
    ext x
    simp [liftTrace]

/-- The own completed row and two possible foreign rows contain the whole
overlap. A nonincident foreign row can be replaced by an arbitrary virtual row. -/
theorem overlap_shape : ∃ S : Finset TracePoint, ∃ u v : TracePoint,
    S.card = 5 ∧ companions ⊆ S ∧
    u ∉ transverse false ∧ v ∉ transverse true ∧
    F.overlapTraces ⊆ commonTraceFamily ∪
      {S, insert u (transverse false), insert v (transverse true)} := by
  have foreign (b : Bool) : ∃ u : TracePoint, u ∉ transverse b ∧
      (foreignIndex b ∈ F.selectedSpines →
        (F.completed (foreignIndex b)).eraseNone = insert u (transverse b)) := by
    by_cases hb : foreignIndex b ∈ F.selectedSpines
    · obtain ⟨u, hu, he⟩ := F.foreign_trace_shape b hb
      exact ⟨u, hu, fun _ => he⟩
    · exact ⟨Sum.inl 0, by simp [transverse], fun h => (hb h).elim⟩
  obtain ⟨u, hu, heu⟩ := foreign false
  obtain ⟨v, hv, hev⟩ := foreign true
  refine ⟨(F.completed 0).eraseNone, u, v,
    F.completed_trace_card F.own_selected, F.companions_subset_own_trace, hu, hv, ?_⟩
  rw [F.overlapTraces_eq]
  apply union_subset subset_union_left
  intro B hB
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hB
  apply mem_union_right
  have hi0 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi0 with rfl | rfl | rfl
  · simp
  · have he := heu hi
    simp only [foreignIndex, Bool.false_eq_true, ↓reduceIte] at he
    simp [he]
  · have he := hev hi
    simp only [foreignIndex, ↓reduceIte] at he
    simp [he]

end OrdinaryRootedFrame

#guard_standard_axioms rooted_spines_cover rooted_core_degree
  OrdinaryRootedFrame.raw_degree_at OrdinaryRootedFrame.degree_label OrdinaryRootedFrame.root_degree
  OrdinaryRootedFrame.own_trace_shape OrdinaryRootedFrame.foreign_trace_shape
  OrdinaryRootedFrame.overlapTraces_eq OrdinaryRootedFrame.exists_foreign_selected
  OrdinaryRootedFrame.mem_overlapTraces_iff OrdinaryRootedFrame.overlap_shape

end CoveringDesigns.C13Structural
