import CoveringDesigns.C14_5_3.LowerBound
import CoveringDesigns.Schoenheim.LowerBound

/-! Direct Schönheim consequence of the universal 41-block lower bound.
Every intermediate ceiling is retained. This is a corollary of the existing
C(14,5,3) ≥ 41 result, not a new lifting mechanism.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(15,6,4) ≥ 103 on arbitrary finite labels. -/
theorem lower_bound_15_6_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 15) (hC : IsCover C 6 4) : 103 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (15 * 41) 6 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 14) (k := 5) (t := 3) (m := 41)
    hv hC (fun {_} _ _ {_} hn hD => C14_5_3.lower_bound hn hD)

end CoveringDesigns
