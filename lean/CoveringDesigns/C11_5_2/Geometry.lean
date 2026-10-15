import CoveringDesigns.C11_5_2.Stanton
import CoveringDesigns.C11_5_2.Geometry.Representatives
import CoveringDesigns.C11_5_2.Geometry.Properties
import CoveringDesigns.C11_5_2.Geometry.FrameLemmas

/-! GPPT's intrinsic short-block and marked-couple geometry, deduced from
the independently proved Stanton theorem. The only fixed calculations inspect
the two displayed representatives, with ordinary kernel proof terms. -/

namespace CoveringDesigns.StantonGeometry

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every intrinsic couple admits the three marked triads and the three
complementary full rows, together with the unique short block. -/
theorem exists_marking_frame {C : Family α}
    (hn : Fintype.card α = 11) (hC : IsCover C 5 2) (hb : C.card = 7)
    {K : Finset α} (hK : IsCouple C K) : Nonempty (MarkingFrame C K) := by
  obtain ⟨tag, e, he⟩ := stanton_classification_on hn hC hb
  have hk : IsCouple (stantonRepresentative tag) (K.map e.toEmbedding) := by
    rw [← he]
    exact (isCouple_relabel e C K).mpr hK
  obtain ⟨F⟩ := representative_marking_frame tag hk
  have hc : relabel e.symm (stantonRepresentative tag) = C := by
    rw [← he, relabel_symm_relabel]
  have hkm : (K.map e.toEmbedding).map e.symm.toEmbedding = K := by simp [map_map]
  simpa only [hc, hkm] using (show Nonempty
    (MarkingFrame (relabel e.symm (stantonRepresentative tag))
      ((K.map e.toEmbedding).map e.symm.toEmbedding)) from ⟨F.relabel e.symm⟩)

/-- The intrinsic geometry holds independently of the chosen Stanton labels. -/
theorem geometry_facts {C : Family α}
    (hn : Fintype.card α = 11) (hC : IsCover C 5 2) (hb : C.card = 7) : Facts C := by
  obtain ⟨tag, e, he⟩ := stanton_classification_on hn hC hb
  have hf := (representative_facts tag).relabel e.symm
  rw [← he, relabel_symm_relabel] at hf
  exact hf

theorem Facts.free_has_spouse {C : Family α} (h : Facts C) {x : α}
    (hx : degree C x = 4) : ∃ y, x ≠ y ∧ IsCouple C {x, y} := by
  rcases h.point_partition x with hs | hy
  · have hd := hs.1
    omega
  · exact hy

/-- A free point has a spouse in an intrinsic couple (GPPT 3.5–3.6). -/
theorem degree_four_has_spouse {C : Family α}
    (hn : Fintype.card α = 11) (hC : IsCover C 5 2) (hb : C.card = 7)
    {x : α} (hx : degree C x = 4) : ∃ y, x ≠ y ∧ IsCouple C {x, y} :=
  (geometry_facts hn hC hb).free_has_spouse hx

theorem Facts.full_intersection_card_le_two {C : Family α} (h : Facts C)
    {B D : Finset α} (hB : B ∈ fullBlocks C) (hD : D ∈ fullBlocks C) (hBD : B ≠ D) :
    (B ∩ D).card ≤ 2 := by
  rcases h.full_intersection B hB D hD hBD with hk | ⟨x, _, he⟩
  · exact le_of_eq hk.1
  · rw [he]
    simp

theorem Facts.couple_full_count_set {C : Family α} (h : Facts C)
    {K : Finset α} (hK : IsCouple C K) : multiplicity (fullBlocks C) K = 3 := by
  obtain ⟨x, y, _, rfl⟩ := card_eq_two.mp hK.1
  exact h.couple_full_count x y hK

theorem Facts.full_pair_count_ne_two_set {C : Family α} (h : Facts C)
    {K : Finset α} (hK : K.card = 2) : multiplicity (fullBlocks C) K ≠ 2 := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hK
  exact h.full_pair_count_ne_two x y hxy

theorem Facts.multiplicity_two_short_set {C : Family α} (h : Facts C)
    {K : Finset α} (hK : K.card = 2) (hm : multiplicity C K = 2) :
    ∃ B ∈ C, IsShortBlock C B ∧ K ⊆ B := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hK
  obtain ⟨B, hB, hs, hx, hy⟩ := h.multiplicity_two_short x y hxy hm
  exact ⟨B, hB, hs, insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hy⟩⟩

#guard_standard_axioms exists_marking_frame geometry_facts degree_four_has_spouse
  Facts.full_pair_count_ne_two_set Facts.multiplicity_two_short_set

end CoveringDesigns.StantonGeometry
