import CoveringDesigns.Qk_K_2.Exclusions
import CoveringDesigns.Multicover.Schoenheim

namespace CoveringDesigns.Qk_K_2
open Schoenheim

/-- Above qk points the elementary two-level Schönheim incidence count is
already strict. No geometric or prime-power assumption is used. -/
theorem indexed_open_floor {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : q*k < Fintype.card X) (hB : Multicover.IsCover B k 2 1) :
    q*(q+1)+1 ≤ Fintype.card I := by
  have hk0 : 0 < k := by omega
  have hk1 : 0 < k-1 := by omega
  have hkx : k ≤ Fintype.card X := by nlinarith
  have hl := Multicover.lower_bound (by omega : 2 ≤ k) hkx hB
  simp only [Multicover.bound_succ,Multicover.bound_zero,Nat.mul_one] at hl
  have hd : q+1 ≤ ceilDiv (Fintype.card X-1) (k-1) := by
    by_contra hn
    have hh := (ceilDiv_le_iff hk1).mp (show ceilDiv (Fintype.card X-1) (k-1) ≤ q by omega)
    have hsub : k-1+1 = k := by omega
    have hx : Fintype.card X-1+1 = Fintype.card X := by omega
    nlinarith
  have hi := (ceilDiv_le_iff hk0).mp hl
  have hm := Nat.mul_le_mul_left (Fintype.card X) hd
  have hstrict := Nat.mul_lt_mul_of_pos_right hv (show 0 < q+1 by omega)
  nlinarith

theorem open_floor {X : Type*} [Fintype X] {C : Family X} {q k : ℕ}
    (hq : 4 ≤ q) (hk : q ≤ k) (hv : q*k < Fintype.card X)
    (hC : IsCover C k 2) : q*(q+1)+1 ≤ C.card := by
  classical
  simpa using indexed_open_floor hq hk hv ((Multicover.ofFamily_isCover_one C k 2).mpr hC)

end CoveringDesigns.Qk_K_2
