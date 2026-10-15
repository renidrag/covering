import CoveringDesigns.C11_5_2
import CoveringDesigns.C12_6_3.Counting

namespace CoveringDesigns

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem degree_at_least_seven_12_6_3 {C : Family α}
    (hn : Fintype.card α = 12) (h : IsCover C 6 3) (p : α) :
    7 ≤ degree C p := by
  have hc : Fintype.card {q : α // q ≠ p} = 11 := by
    rw [complement_point_card, hn]
  have hl := lower_bound_11_5_2 hc (link_isCover h p)
  rwa [link_card] at hl

theorem lower_bound_12_6_3_schonheim {C : Family α}
    (hn : Fintype.card α = 12) (h : IsCover C 6 3) : 14 ≤ C.card := by
  have hl := incidence_lower_bound h.1 (degree_at_least_seven_12_6_3 hn h)
  rw [hn] at hl
  omega

end CoveringDesigns
