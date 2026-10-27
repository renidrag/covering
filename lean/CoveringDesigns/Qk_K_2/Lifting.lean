import CoveringDesigns.C4k_K_2.LowerBound
import CoveringDesigns.Multicover.Schoenheim

/-! Schönheim iteration of the unchanged order-four seed. The recurrence is
the established Multicover.bound; no ceilings are collapsed. -/
namespace CoveringDesigns.Qk_K_2

theorem lifted_lower_bound {α : Type*} [Fintype α] {C : Family α}
    (k : ℕ) (hk : 8 ≤ k) (hnd : ¬ 4 ∣ k) (j : ℕ)
    (hv : Fintype.card α = 4*k+j) (hC : IsCover C (k+j) (2+j)) :
    Multicover.bound 21 (4*k+j) (k+j) j ≤ C.card := by
  classical
  induction j generalizing α with
  | zero => simpa [hnd] using C4k_K_2.lower_bound hk hv hC
  | succ j ih =>
    rw [Multicover.bound_succ]
    simpa only [Nat.add_succ,Nat.add_zero,Nat.succ_sub_one] using
      (Schoenheim.lift_lower_bound (v := 4*k+j) (k := k+j) (t := 2+j)
        (by simpa only [Nat.add_succ] using hv)
        (by simpa only [Nat.add_succ] using hC)
        (fun {_} _ _ {_} hn hD => ih hn hD))

end CoveringDesigns.Qk_K_2
