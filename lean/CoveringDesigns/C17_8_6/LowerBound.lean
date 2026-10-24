import CoveringDesigns.C16_7_5.LowerBound

/-! Direct Schönheim consequence of the universal 236-block lower bound.
Every intermediate ceiling is retained. This is a corollary of the existing
C(14,5,3) ≥ 41 result, not a new lifting mechanism.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(17,8,6) ≥ 502 on arbitrary finite labels. -/
theorem lower_bound_17_8_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 17) (hC : IsCover C 8 6) : 502 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (17 * 236) 8 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 16) (k := 7) (t := 5) (m := 236)
    hv hC (fun {_} _ _ {_} hn hD => lower_bound_16_7_5 hn hD)

end CoveringDesigns
