import CoveringDesigns.C13_7_4.Structural.PairBounds
import CoveringDesigns.C13_7_4.Structural.TenPair
import CoveringDesigns.C13_7_4.Structural.OverlapAlignment
import CoveringDesigns.C13_7_4.Structural.SharedForeign
import CoveringDesigns.C13_7_4.Structural.AlignedRows
import CoveringDesigns.C13_7_4.Structural.AlignedDegrees

/-! Compatibility of actual minimum links in a thirteen-point covering. -/

namespace CoveringDesigns.C13Structural
open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An actual pair of multiplicity eight or nine has two ordinary rooted
frames. Both frames retain the original global covering and the same roots. -/
theorem ordinary_pair_frames {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) {p q : α}
    (hp : degree C p = 15) (hq : degree C q = 15) (hpq : p ≠ q)
    (hd : degree (star C p) q = 8 ∨ degree (star C p) q = 9) :
    Nonempty (OrdinaryRootedFrame (link C p) ⟨q, hpq.symm⟩ ×
      OrdinaryRootedFrame (link C q) ⟨p, hpq⟩) := by
  obtain ⟨F⟩ := ordinary_rooted_frame_of_isomorphic_template
    (ordinary_link_of_pair_eight_or_nine hn hC hp hpq hd) ⟨q, hpq.symm⟩
  have hd' : degree (star C q) p = 8 ∨ degree (star C q) p = 9 := by
    rwa [pair_degree_comm]
  obtain ⟨G⟩ := ordinary_rooted_frame_of_isomorphic_template
    (ordinary_link_of_pair_eight_or_nine hn hC hq hpq.symm hd') ⟨p, hpq⟩
  exact ⟨(F, G)⟩

/-- One shared foreign completion treats both high ordinary multiplicities.
Two of the three completed rows agree, so all points avoiding them have
pair degree seven with both roots, irrespective of the third completion. -/
theorem ordinary_high_pair_impossible {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hb : C.card ≤ 29)
    {p q : α} {hpq : p ≠ q}
    (F : OrdinaryRootedFrame (link C p) ⟨q, hpq.symm⟩)
    (G : OrdinaryRootedFrame (link C q) ⟨p, hpq⟩)
    (hd : 8 ≤ degree (link C p) ⟨q, hpq.symm⟩) : False := by
  let e := traceTransition F G
  have he : relabel e commonTraceFamily = commonTraceFamily :=
    traceTransition_preserves_core F G
  obtain ⟨b, c, u, v, hbsel, _, hu, hv, hshapeF, hshapeG, hrow⟩ :=
    F.shared_foreign_of_overlap_transport G e he (traceTransition_mem_overlap F G) hd
  rcases private_alignment_of_shared_foreign e he b c u v hu hv hrow with hi | hs
  · exact identical_private_cores_impossible hn hC hb F.globalLabel
      (identical_rows_of_private_alignment F G hi)
  · obtain ⟨huX, _, hprivate⟩ := hs
    obtain ⟨j, rfl⟩ := exists_spouse_opposite_half b u huX hu
    have hprivate' : relabel (traceTransition F G) privateTraceFamily =
        relabel (Equiv.swap (Sum.inr (j, !b)) (Sum.inr (j, b))) privateTraceFamily := by
      simpa only [e, spouseMate_spouse, Bool.not_not] using hprivate
    obtain ⟨A, hA, hcard, hown⟩ := F.own_trace_shape
    have H := aligned_swap_rows F G j b A hA hcard hown hprivate'
    apply spouse_swap_impossible hn hC hb
      ((pairNormalization j b).trans F.globalLabel) (normalizedAdditions j b A) H
      (normalized_foreign_row (hpq := hpq) F j b hbsel hshapeF)
    intro w hw hwR
    let x : TracePoint := normalizeTrace j b (Sum.inr (w, true))
    have hx : x ∈ transverse (!b) := normalization_other_half j b w
    have hxR : x ∉ A := by
      intro h
      exact hwR ((mem_normalizedAdditions_iff j b A (w, true)).mpr h)
    have hxu : x ≠ Sum.inr (j, !b) := normalization_other_ne_extra j b w hw
    have hf : ((G.completed (foreignIndex c)).eraseNone).map
        (traceTransition F G).toEmbedding = (F.completed (foreignIndex b)).eraseNone := by
      rw [hshapeG, hshapeF]
      exact hrow
    have hdegrees := pair_degrees_seven_of_shared_shapes F G b c A
      (Sum.inr (j, !b)) hown hshapeF hf hx hxR hxu
    change degree (star C (F.globalLabel (Sum.inl false))) (F.globalLabel (Sum.inr x)) = 7 ∧
      degree (star C (F.globalLabel (Sum.inl true))) (F.globalLabel (Sum.inr x)) = 7
    rw [F.globalLabel_false, F.globalLabel_true]
    exact hdegrees

/-- Distinct minimum points in a covering with at most twenty-nine blocks
must have pair multiplicity seven. All GPPT compatibility cases are discharged. -/
theorem minimum_pair_degree_seven {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hb : C.card ≤ 29)
    {p q : α} (hp : degree C p = 15) (hq : degree C q = 15) (hpq : p ≠ q) :
    degree (star C p) q = 7 := by
  have hoptions := minimum_pair_options hn hC hp hpq
  have hnot10 := minimum_pair_ne_ten hn hC hb hp hq hpq
  by_contra hnot7
  have h89 : degree (star C p) q = 8 ∨ degree (star C p) q = 9 := by omega
  obtain ⟨F, G⟩ := ordinary_pair_frames hn hC hp hq hpq h89
  have h8 : 8 ≤ degree (star C p) q := by omega
  exact ordinary_high_pair_impossible hn hC hb F G (by simpa only [degree_link] using h8)

#guard_standard_axioms ordinary_pair_frames ordinary_high_pair_impossible
  minimum_pair_degree_seven

end CoveringDesigns.C13Structural
