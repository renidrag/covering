import CoveringDesigns.C36_20_5.LowerBound

/-! Direct Schönheim consequence of the universal 44-block lower bound.
Every intermediate ceiling is retained, starting from C(34,18,3) ≥ 13.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(37,21,6) ≥ 78 on arbitrary finite labels. -/
theorem lower_bound_37_21_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 37) (hC : IsCover C 21 6) : 78 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (37 * 44) 21 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 36) (k := 20) (t := 5) (m := 44)
    hv hC (fun {_} _ _ {_} hn hD => lower_bound_36_20_5 hn hD)

end CoveringDesigns
