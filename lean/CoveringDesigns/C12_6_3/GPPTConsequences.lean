import CoveringDesigns.C12_6_3.SmallBounds
import CoveringDesigns.C11_5_2

/-! Necessary conditions for a degree-seven point in a (12,6,3) covering. -/

namespace CoveringDesigns

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem minimum_pair_degree_le_four {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    {p q : α} (hp : degree C p = 7) (hq : q ≠ p) :
    degree (star C p) q ≤ 4 := by
  have hh := stanton_degree_bound_on
    (by rw [complement_point_card, hn]) (link_isCover hC p)
    (by rwa [link_card]) (⟨q, hq⟩ : {q : α // q ≠ p})
  rwa [degree_link] at hh

theorem minimum_point_intersection_le_four {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    {p : α} (hp : degree C p = 7)
    {B D : Finset α} (hB : B ∈ C) (hD : D ∈ C) (hBD : B ≠ D)
    (hpB : p ∈ B) (hpD : p ∈ D) : (B ∩ D).card ≤ 4 := by
  have hBl : B.subtype (· ≠ p) ∈ link C p :=
    mem_image.mpr ⟨B, mem_filter.mpr ⟨hB, hpB⟩, rfl⟩
  have hDl : D.subtype (· ≠ p) ∈ link C p :=
    mem_image.mpr ⟨D, mem_filter.mpr ⟨hD, hpD⟩, rfl⟩
  have hneq : B.subtype (· ≠ p) ≠ D.subtype (· ≠ p) := by
    intro he
    apply hBD
    ext q
    by_cases hq : q = p
    · simpa [hq] using iff_of_true hpB hpD
    · have hh := congrArg (fun S => (⟨q, hq⟩ : {q : α // q ≠ p}) ∈ S) he
      simpa using hh
  have hh := stanton_intersection_bound_on
    (by rw [complement_point_card, hn]) (link_isCover hC p)
    (by rwa [link_card]) hBl hDl hneq
  have he : B.subtype (· ≠ p) ∩ D.subtype (· ≠ p) = (B ∩ D).subtype (· ≠ p) := by
    ext q
    simp
  rw [he, card_subtype] at hh
  have hf : (B ∩ D).filter (· ≠ p) = (B ∩ D).erase p := by
    ext q
    simp [and_comm]
  rw [hf, card_erase_of_mem (mem_inter.mpr ⟨hpB, hpD⟩)] at hh
  omega

theorem six_minimum_points_at_most_fifteen {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15) :
    6 ≤ (minimumPoints C 7).card := by
  have h := minimum_points_bound hC.1 (degree_at_least_seven_12_6_3 hn hC)
  rw [hn] at h
  omega

end CoveringDesigns
