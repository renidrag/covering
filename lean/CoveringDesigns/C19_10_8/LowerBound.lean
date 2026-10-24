import CoveringDesigns.C18_9_7.LowerBound

/-! Direct Schönheim consequence of the universal 1004-block lower bound.
Every intermediate ceiling is retained. This is a corollary of the existing
C(14,5,3) ≥ 41 result, not a new lifting mechanism.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(19,10,8) ≥ 1908 on arbitrary finite labels. -/
theorem lower_bound_19_10_8 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 19) (hC : IsCover C 10 8) : 1908 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (19 * 1004) 10 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 18) (k := 9) (t := 7) (m := 1004)
    hv hC (fun {_} _ _ {_} hn hD => lower_bound_18_9_7 hn hD)

end CoveringDesigns
