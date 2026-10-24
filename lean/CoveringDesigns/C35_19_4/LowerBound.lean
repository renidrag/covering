import CoveringDesigns.C34_18_3.LowerBound
import CoveringDesigns.Schoenheim.LowerBound

/-! Direct Schönheim consequence of the universal 13-block lower bound.
Every intermediate ceiling is retained, starting from C(34,18,3) ≥ 13.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(35,19,4) ≥ 24 on arbitrary finite labels. -/
theorem lower_bound_35_19_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 35) (hC : IsCover C 19 4) : 24 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (35 * 13) 19 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 34) (k := 18) (t := 3) (m := 13)
    hv hC (fun {_} _ _ {_} hn hD => lower_bound_34_18_3 hn hD)

end CoveringDesigns
