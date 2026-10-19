import CoveringDesigns.C20_11_3.Rank
import CoveringDesigns.C20_11_3.Saturated

/-!
The unconditional lower bound on arbitrary twenty-point labels. The point
incidence bound excludes every smaller family; at eleven blocks the rank
argument forces a saturated pair and the shared-block count excludes it.
-/

namespace CoveringDesigns

/-- Every ordinary triple covering by eleven-point blocks on twenty points
has at least twelve blocks. There are no structural or rank assumptions. -/
theorem lower_bound_20_11_3 {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} (hv : Fintype.card α = 20) (hC : IsCover C 11 3) :
    12 ≤ C.card := by
  have h11 := C20_11_3.eleven_le_card hv hC
  by_contra h12
  have hb : C.card = 11 := by omega
  obtain ⟨p, q, hpq, hs⟩ := C20_11_3.exists_saturated_pair hv hC hb
  exact C20_11_3.no_saturated_pair hv hC hb hpq hs

end CoveringDesigns
