import CoveringDesigns.C12_6_3.Structural.Reduction
import CoveringDesigns.Foundations.FourSetCounting

/-!
Incidence consequences needed by the structural thirteen-point proof.
Only the structural Stanton and GPPT theorems are used, not their finite
completion catalogue.
-/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every point link has at least fifteen blocks. -/
theorem degree_lower {C : Family α} (hn : Fintype.card α = 13)
    (hC : IsCover C 7 4) (p : α) : 15 ≤ degree C p := by
  have h := lower_bound_fifteen (by rw [complement_point_card, hn]) (link_isCover hC p)
  rwa [link_card] at h

/-- The excess above the point-degree lower bound leaves five minimum points. -/
theorem five_minimum_points {C : Family α} (hn : Fintype.card α = 13)
    (hC : IsCover C 7 4) (hb : C.card ≤ 29) :
    5 ≤ (minimumPoints C 15).card := by
  have h := minimum_points_bound hC.1 (degree_lower hn hC)
  rw [hn] at h
  omega

omit [Fintype α] in
/-- Containment counts commute with passing to a point link. -/
theorem containmentCount_link (C : Family α) (p : α)
    (S : Finset {q : α // q ≠ p}) :
    containmentCount (link C p) S =
      containmentCount C (insert p (S.map (Function.Embedding.subtype _))) := by
  have he : ((link C p).filter (S ⊆ ·)).image (liftBlock p) =
      C.filter (insert p (S.map (Function.Embedding.subtype _)) ⊆ ·) := by
    ext B
    constructor
    · intro h
      obtain ⟨D, hD, rfl⟩ := mem_image.mp h
      obtain ⟨hD, hSD⟩ := mem_filter.mp hD
      have hmem : liftBlock p D ∈ star C p := by
        rw [← liftBlock_link]
        exact mem_image.mpr ⟨D, hD, rfl⟩
      refine mem_filter.mpr ⟨(mem_filter.mp hmem).1, ?_⟩
      exact (liftBlock_subset_iff p S D).mpr hSD
    · intro h
      obtain ⟨hB, hs⟩ := mem_filter.mp h
      have hp : p ∈ B := hs (mem_insert_self _ _)
      refine mem_image.mpr ⟨B.subtype (· ≠ p), mem_filter.mpr ⟨?_, ?_⟩,
        liftBlock_subtype p hp⟩
      · exact mem_image.mpr ⟨B, mem_filter.mpr ⟨hB, hp⟩, rfl⟩
      · apply (liftBlock_subset_iff p S _).mp
        rwa [liftBlock_subtype p hp]
  unfold containmentCount
  rw [← he, card_image_of_injective _ (liftBlock_injective p)]

/-- Three minimum points joined by degree-seven pairs occur three times.
Only the two pairs through the displayed root are needed. -/
theorem minimum_triple_count {C : Family α} (hn : Fintype.card α = 13)
    (hC : IsCover C 7 4) {p q r : α}
    (hp : degree C p = 15) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hqp : degree (star C p) q = 7) (hrp : degree (star C p) r = 7) :
    containmentCount C {p, q, r} = 3 := by
  let q' : {x : α // x ≠ p} := ⟨q, hpq.symm⟩
  let r' : {x : α // x ≠ p} := ⟨r, hpr.symm⟩
  have hq' : degree (link C p) q' = 7 := by rwa [degree_link]
  have hr' : degree (link C p) r' = 7 := by rwa [degree_link]
  have he := minimum_pair_degree_three
    (by rw [complement_point_card, hn] : Fintype.card {x : α // x ≠ p} = 12)
    (link_isCover hC p) (by rw [link_card, hp]) hq' hr'
    (fun h => hqr (congrArg Subtype.val h))
  rw [← containmentCount_pair, containmentCount_link] at he
  simpa [q', r'] using he

omit [Fintype α] in
/-- Any four covered points occur at least once. -/
theorem quadruple_count_pos {C : Family α} (hC : IsCover C 7 4)
    {S : Finset α} (hS : S.card = 4) : 1 ≤ containmentCount C S := by
  obtain ⟨B, hB, hs⟩ := hC.2 S hS
  exact card_pos.mpr ⟨B, mem_filter.mpr ⟨hB, hs⟩⟩

/-- With degree-seven root pairs, a quadruple occurs either once or three times. -/
theorem minimum_quad_count_one_or_three {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) {p q r s : α}
    (hp : degree C p = 15)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hqp : degree (star C p) q = 7) (hrp : degree (star C p) r = 7)
    (hsp : degree (star C p) s = 7) :
    containmentCount C {p, q, r, s} = 1 ∨ containmentCount C {p, q, r, s} = 3 := by
  let q' : {x : α // x ≠ p} := ⟨q, hpq.symm⟩
  let r' : {x : α // x ≠ p} := ⟨r, hpr.symm⟩
  let s' : {x : α // x ≠ p} := ⟨s, hps.symm⟩
  have hq' : degree (link C p) q' = 7 := by rwa [degree_link]
  have hr' : degree (link C p) r' = 7 := by rwa [degree_link]
  have hs' : degree (link C p) s' = 7 := by rwa [degree_link]
  have he : containmentCount (link C p) {q', r', s'} =
      containmentCount C {p, q, r, s} := by
    rw [containmentCount_link]
    simp [q', r', s']
  have hpos := quadruple_count_pos hC
    (S := {p, q, r, s}) (by simp [hpq, hpr, hps, hqr, hqs, hrs])
  by_cases ht : 2 ≤ containmentCount C {p, q, r, s}
  · right
    rw [← he]
    apply repeated_minimum_triple_count
      (by rw [complement_point_card, hn]) (link_isCover hC p)
      (by rw [link_card, hp])
    · have hqr' : q' ≠ r' := fun h => hqr (congrArg Subtype.val h)
      have hqs' : q' ≠ s' := fun h => hqs (congrArg Subtype.val h)
      have hrs' : r' ≠ s' := fun h => hrs (congrArg Subtype.val h)
      simp [hqr', hqs', hrs']
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hq'
      · exact hr'
      · exact hs'
    · rwa [he]
  · left
    omega

#guard_standard_axioms degree_lower five_minimum_points containmentCount_link
  minimum_triple_count quadruple_count_pos minimum_quad_count_one_or_three

end CoveringDesigns.C13Structural
