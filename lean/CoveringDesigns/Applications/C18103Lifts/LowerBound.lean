import CoveringDesigns.C18_10_3.LowerBound
import CoveringDesigns.Multicover.Schoenheim

/-! Schönheim iteration from the unconditional structural seed C(18,10,3) ≥ 12.
This is an application of the existing iteration, with every ceiling retained.
Structural argument and formalisation: Rob Gardiner, with AI assistance.
The lifting theorem is due to J. Schönheim. -/
namespace CoveringDesigns.Applications.C18103Lifts

/-- The seed is proved internally; callers supply only point count and coverage. -/
theorem lower_bound {α : Type*} [Fintype α] {C : Family α} (s : ℕ)
    (hv : Fintype.card α = 18 + s) (hC : IsCover C (10 + s) (3 + s)) :
    Multicover.bound 12 (18 + s) (10 + s) s ≤ C.card := by
  classical
  induction s generalizing α with
  | zero => exact lower_bound_18_10_3 hv hC
  | succ s ih =>
    rw [Multicover.bound_succ]
    simpa only [Nat.add_succ,Nat.add_zero,Nat.succ_sub_one] using
      (Schoenheim.lift_lower_bound (v := 18+s) (k := 10+s) (t := 3+s)
        (by simpa only [Nat.add_succ] using hv)
        (by simpa only [Nat.add_succ] using hC)
        (fun {_} _ _ {_} hn hD => ih hn hD))

end CoveringDesigns.Applications.C18103Lifts
