import CoveringDesigns.Foundations.Basic

namespace CoveringDesigns

theorem six_minimum_points_of_15 {C : Family (Fin 12)}
    (hu : Uniform C 6) (hb : C.card = 15) (hl : ∀ p, 7 ≤ degree C p) :
    6 ≤ (minimumPoints C 7).card := by
  have h := minimum_points_bound hu hl
  simp only [Fintype.card_fin, hb] at h
  omega

end CoveringDesigns
