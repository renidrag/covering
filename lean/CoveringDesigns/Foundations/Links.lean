import CoveringDesigns.Foundations.Basic

/-! Deleting a point preserves the covering property and the star's cardinality. -/

namespace CoveringDesigns

open Finset

variable {α : Type*} [DecidableEq α]

def link (C : Family α) (p : α) : Family {q : α // q ≠ p} :=
  (star C p).image (Finset.subtype (· ≠ p))

theorem link_card (C : Family α) (p : α) : (link C p).card = degree C p := by
  apply card_image_iff.mpr
  intro B hB D hD h
  have hpB : p ∈ B := (mem_filter.mp hB).2
  have hpD : p ∈ D := (mem_filter.mp hD).2
  ext q
  by_cases hq : q = p
  · simpa [hq] using iff_of_true hpB hpD
  · have hh := congrArg (fun S => (⟨q, hq⟩ : {q : α // q ≠ p}) ∈ S) h
    simpa using hh

theorem link_uniform {C : Family α} {k : ℕ} (hu : Uniform C (k + 1)) (p : α) :
    Uniform (link C p) k := by
  intro D hD
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hD
  obtain ⟨hBC, hpB⟩ := mem_filter.mp hB
  rw [card_subtype]
  have he : B.filter (· ≠ p) = B.erase p := by
    ext q
    simp [and_comm]
  rw [he, card_erase_of_mem hpB, hu B hBC]
  omega

theorem link_covers {C : Family α} {t : ℕ} (hc : Covers C (t + 1)) (p : α) :
    Covers (link C p) t := by
  intro T hT
  let e : {q : α // q ≠ p} ↪ α := Function.Embedding.subtype _
  have hpT : p ∉ T.map e := by
    intro h
    obtain ⟨q, _, hq⟩ := mem_map.mp h
    exact q.property hq
  have ht : (insert p (T.map e)).card = t + 1 := by
    rw [card_insert_of_notMem hpT, card_map, hT]
  obtain ⟨B, hBC, hTB⟩ := hc _ ht
  refine ⟨B.subtype (· ≠ p), mem_image.mpr ⟨B, ?_, rfl⟩, ?_⟩
  · exact mem_filter.mpr ⟨hBC, hTB (mem_insert_self _ _)⟩
  · intro q hq
    exact mem_subtype.mpr (hTB (mem_insert_of_mem (mem_map.mpr ⟨q, hq, rfl⟩)))

theorem link_isCover {C : Family α} {k t : ℕ} (h : IsCover C (k + 1) (t + 1))
    (p : α) : IsCover (link C p) k t :=
  ⟨link_uniform h.1 p, link_covers h.2 p⟩

theorem complement_point_card [Fintype α] (p : α) :
    Fintype.card {q : α // q ≠ p} = Fintype.card α - 1 := by
  simp [Fintype.card_subtype_compl]

theorem star_link (C : Family α) (p : α) (q : {q : α // q ≠ p}) :
    star (link C p) q = link (star C q.val) p := by
  unfold star link
  rw [filter_image]
  congr 1
  ext B
  simp [star, and_comm, and_left_comm]

theorem pair_degree_comm (C : Family α) (p q : α) :
    degree (star C p) q = degree (star C q) p := by
  unfold degree star
  congr 1
  ext B
  simp [and_comm, and_left_comm]

theorem degree_link (C : Family α) (p : α) (q : {q : α // q ≠ p}) :
    degree (link C p) q = degree (star C p) q.val := by
  unfold degree
  rw [star_link, link_card]
  exact pair_degree_comm C q.val p

end CoveringDesigns
