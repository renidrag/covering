import CoveringDesigns.C17_8_6.LowerBound

/-! Direct Schönheim consequence of the universal 502-block lower bound.
Every intermediate ceiling is retained. This is a corollary of the existing
C(14,5,3) ≥ 41 result, not a new lifting mechanism.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(18,9,7) ≥ 1004 on arbitrary finite labels. -/
theorem lower_bound_18_9_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 9 7) : 1004 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (18 * 502) 9 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 17) (k := 8) (t := 6) (m := 502)
    hv hC (fun {_} _ _ {_} hn hD => lower_bound_17_8_6 hn hD)

end CoveringDesigns
