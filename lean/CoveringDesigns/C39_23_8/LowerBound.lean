import CoveringDesigns.C38_22_7.LowerBound

/-! Direct Schönheim consequence of the universal 135-block lower bound.
Every intermediate ceiling is retained, starting from C(34,18,3) ≥ 13.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(39,23,8) ≥ 229 on arbitrary finite labels. -/
theorem lower_bound_39_23_8 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 39) (hC : IsCover C 23 8) : 229 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (39 * 135) 23 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 38) (k := 22) (t := 7) (m := 135)
    hv hC (fun {_} _ _ {_} hn hD => lower_bound_38_22_7 hn hD)

end CoveringDesigns
