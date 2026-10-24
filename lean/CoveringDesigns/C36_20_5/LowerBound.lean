import CoveringDesigns.C35_19_4.LowerBound

/-! Direct Schönheim consequence of the universal 24-block lower bound.
Every intermediate ceiling is retained, starting from C(34,18,3) ≥ 13.
Formalisation: Rob Gardiner, with AI assistance; lifting: J. Schönheim. -/
namespace CoveringDesigns

/-- C(36,20,5) ≥ 44 on arbitrary finite labels. -/
theorem lower_bound_36_20_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 36) (hC : IsCover C 20 5) : 44 ≤ C.card := by
  classical
  change Schoenheim.ceilDiv (36 * 24) 20 ≤ C.card
  exact Schoenheim.lift_lower_bound (v := 35) (k := 19) (t := 4) (m := 24)
    hv hC (fun {_} _ _ {_} hn hD => lower_bound_35_19_4 hn hD)

end CoveringDesigns
