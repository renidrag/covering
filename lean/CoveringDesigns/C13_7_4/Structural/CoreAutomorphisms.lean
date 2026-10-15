import CoveringDesigns.C13_7_4.Structural.RootedCore
import CoveringDesigns.C13_7_4.Structural.CoreGluing

/-!
The companion points and spouse pairs are recognized intrinsically by their
columns in the six-row core. Thus every core-preserving relabelling sends
transverse halves to transverse halves. No automorphisms are enumerated.
-/

namespace CoveringDesigns.C13Structural

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

/-- The eight points outside the root's own spine. -/
def spouseGround : Finset TracePoint := univ \ companions

/-- Companions are fixed; each of the four equal-column spouse pairs is
interchanged. -/
def spouseMate : TracePoint → TracePoint
  | Sum.inl m => Sum.inl m
  | Sum.inr (v, b) => Sum.inr (v, !b)

@[simp] theorem spouseMate_companion (m : Fin 3) :
    spouseMate (Sum.inl m) = Sum.inl m := rfl

@[simp] theorem spouseMate_spouse (v : Fin 4) (b : Bool) :
    spouseMate (Sum.inr (v, b)) = Sum.inr (v, !b) := rfl

theorem spouseMate_involutive : Function.Involutive spouseMate := by
  intro x
  rcases x with m | ⟨v, b⟩ <;> simp [spouseMate]

private theorem core_degree_two_iff :
    ∀ x : TracePoint, degree commonTraceFamily x = 2 ↔ x ∈ companions := by decide +kernel

private theorem core_star_eq_iff :
    ∀ x y : TracePoint,
      star commonTraceFamily y = star commonTraceFamily x ↔
        y = x ∨ y = spouseMate x := by decide +kernel

private theorem spouseMate_fixed_iff :
    ∀ x : TracePoint, spouseMate x = x ↔ x ∈ companions := by decide +kernel

theorem canonical_transverse :
    ∀ b, IsTransverse spouseGround spouseMate (transverse b) := by
  unfold IsTransverse
  decide +kernel

/-- The three degree-two columns are exactly the companions, so they are
preserved by every relabelling preserving the six core rows. -/
theorem core_preserving_companion_mem
    (e : Equiv.Perm TracePoint) (he : relabel e commonTraceFamily = commonTraceFamily)
    (x : TracePoint) : e x ∈ companions ↔ x ∈ companions := by
  have hd := degree_relabel e commonTraceFamily x
  rw [he] at hd
  rw [← core_degree_two_iff, ← core_degree_two_iff, hd]

theorem core_preserving_map_companions
    (e : Equiv.Perm TracePoint) (he : relabel e commonTraceFamily = commonTraceFamily) :
    companions.map e.toEmbedding = companions := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp only [mem_map_equiv, Equiv.symm_apply_apply]
  exact (core_preserving_companion_mem e he y).symm

theorem core_preserving_map_spouseGround
    (e : Equiv.Perm TracePoint) (he : relabel e commonTraceFamily = commonTraceFamily) :
    spouseGround.map e.toEmbedding = spouseGround := by
  rw [spouseGround, map_sdiff, map_univ_equiv, core_preserving_map_companions e he]

/-- Equal degree-three columns recognize the four spouse pairs. -/
theorem core_preserving_spouseMate
    (e : Equiv.Perm TracePoint) (he : relabel e commonTraceFamily = commonTraceFamily)
    (x : TracePoint) : e (spouseMate x) = spouseMate (e x) := by
  by_cases hx : spouseMate x = x
  · have hcomp := (spouseMate_fixed_iff x).mp hx
    have hecomp := (core_preserving_companion_mem e he x).mpr hcomp
    rw [hx, (spouseMate_fixed_iff (e x)).mpr hecomp]
  · have hs : star commonTraceFamily (spouseMate x) = star commonTraceFamily x :=
      (core_star_eq_iff x (spouseMate x)).mpr (Or.inr rfl)
    have hse : star commonTraceFamily (e (spouseMate x)) = star commonTraceFamily (e x) := by
      rw [← he, star_relabel, star_relabel, hs]
    rcases (core_star_eq_iff (e x) (e (spouseMate x))).mp hse with h | h
    · exact False.elim (hx (e.injective h))
    · exact h

/-- A core automorphism sends either foreign spine to a transverse half. -/
theorem core_preserving_transverse
    (e : Equiv.Perm TracePoint) (he : relabel e commonTraceFamily = commonTraceFamily)
    (b : Bool) :
    IsTransverse spouseGround spouseMate ((transverse b).map e.toEmbedding) := by
  refine ⟨?_, ?_⟩
  · rw [← core_preserving_map_spouseGround e he]
    exact map_subset_map.mpr (canonical_transverse b).1
  · intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : y ∈ spouseGround := by
      rw [← core_preserving_map_spouseGround e he] at hx
      simpa only [mem_map_equiv, Equiv.symm_apply_apply] using hx
    rw [← core_preserving_spouseMate e he y]
    simpa only [mem_map_equiv, Equiv.symm_apply_apply] using (canonical_transverse b).2 y hy

/-- A single shared foreign row aligns transverse halves. This is the
uniform gluing conclusion for both eight- and nine-row overlaps. -/
theorem core_preserving_shared_foreign
    (e : Equiv.Perm TracePoint) (he : relabel e commonTraceFamily = commonTraceFamily)
    (b c : Bool) (u v : TracePoint)
    (hu : u ∉ transverse b) (hv : v ∉ transverse c)
    (hrow : (insert v (transverse c)).map e.toEmbedding = insert u (transverse b)) :
    (transverse c).map e.toEmbedding = transverse b ∨
      (u ∈ spouseGround ∧ e v = spouseMate u ∧
        (transverse c).map e.toEmbedding = insert u ((transverse b).erase (spouseMate u))) := by
  apply transverse_extension_unique_or_swap (canonical_transverse b)
    (core_preserving_transverse e he c) hu
  · simpa only [mem_map_equiv, Equiv.symm_apply_apply] using hv
  · simpa only [map_insert, Equiv.coe_toEmbedding] using hrow.symm

/-- Swapping points with identical columns preserves the whole family. -/
theorem relabel_swap_eq_of_star_eq {α : Type*} [DecidableEq α]
    (C : Family α) (u v : α) (hstar : star C u = star C v) :
    relabel (Equiv.swap u v) C = C := by
  have hmem (B : Finset α) (hB : B ∈ C) : u ∈ B ↔ v ∈ B := by
    have hu : u ∈ B ↔ B ∈ star C u := by simp [star, hB]
    have hv : v ∈ B ↔ B ∈ star C v := by simp [star, hB]
    exact hu.trans (hstar ▸ hv.symm)
  have hmap (B : Finset α) (hB : B ∈ C) : B.map (Equiv.swap u v).toEmbedding = B := by
    ext x
    by_cases hxu : x = u
    · subst x
      simpa using (hmem B hB).symm
    by_cases hxv : x = v
    · subst x
      simpa using hmem B hB
    simp [Equiv.swap_apply_def, hxu, hxv]
  unfold relabel
  rw [map_eq_image]
  exact (image_congr hmap).trans image_id

/-- Every individual spouse swap fixes the six common full rows. -/
theorem spouse_swap_preserves_core (x : TracePoint) :
    relabel (Equiv.swap x (spouseMate x)) commonTraceFamily = commonTraceFamily := by
  apply relabel_swap_eq_of_star_eq
  exact ((core_star_eq_iff x (spouseMate x)).mpr (Or.inr rfl)).symm

#guard_standard_axioms core_preserving_map_companions core_preserving_map_spouseGround
  core_preserving_spouseMate core_preserving_transverse core_preserving_shared_foreign
  relabel_swap_eq_of_star_eq spouse_swap_preserves_core

end CoveringDesigns.C13Structural
