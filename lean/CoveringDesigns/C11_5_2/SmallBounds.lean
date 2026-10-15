import CoveringDesigns.Foundations.Bounds

namespace CoveringDesigns

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem degree_at_least_three_11_5_2 {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (p : α) :
    3 ≤ degree C p := by
  have hl := one_cover_bound (link_isCover h p)
  rw [complement_point_card, hn, link_card] at hl
  omega

theorem lower_bound_11_5_2 {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) : 7 ≤ C.card := by
  have hl := incidence_lower_bound h.1 (degree_at_least_three_11_5_2 hn h)
  rw [hn] at hl
  omega

end CoveringDesigns
