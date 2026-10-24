import CoveringDesigns.C15_6_4.LowerBound

/-! Direct Schönheim consequence of the universal 103-block lower bound.
Every intermediate ceiling is retained. This is a corollary of the existing
C(14,5,3) ≥ 41 result, not a new lifting mechanism.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(16,7,5) ≥ 236 on arbitrary finite labels. -/
theorem lower_bound_16_7_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 16) (hC : IsCover C 7 5) : 236 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (16 * 103) 7 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 15) (k := 6) (t := 4) (m := 103)
    hv hC (fun {_} _ _ {_} hn hD => lower_bound_15_6_4 hn hD)

end CoveringDesigns
