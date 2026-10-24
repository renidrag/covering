import CoveringDesigns.C37_21_6.LowerBound

/-! Direct Schönheim consequence of the universal 78-block lower bound.
Every intermediate ceiling is retained, starting from C(34,18,3) ≥ 13.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(38,22,7) ≥ 135 on arbitrary finite labels. -/
theorem lower_bound_38_22_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 38) (hC : IsCover C 22 7) : 135 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (38 * 78) 22 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 37) (k := 21) (t := 6) (m := 78)
    hv hC (fun {_} _ _ {_} hn hD => lower_bound_37_21_6 hn hD)

end CoveringDesigns
