import CoveringDesigns.PairDivisibility
import CoveringDesigns.TwistedArithmetic.OrderFour

namespace CoveringDesigns.C4k_K_2
open TruncatedPlaneLoads PairDivisibility
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
variable {k : ℕ} {B : I → Finset X}

theorem indexed_twenty (hk : 4 ≤ k) (hv : Fintype.card X = 4*k)
    (hB : Multicover.IsCover B k 2 1) : 20 ≤ Fintype.card I :=
  incidence_floor (by decide) hk hv hB

theorem indexed_twenty_one (hk : 4 ≤ k) (hv : Fintype.card X = 4*k)
    (hB : Multicover.IsCover B k 2 1) (hnd : ¬ 4 ∣ k) : 21 ≤ Fintype.card I := by
  have hf := indexed_twenty hk hv hB
  have hn : Fintype.card I ≠ 20 := by
    intro he
    exact TwistedArithmetic.no_twisted_four
      (twisted_of_not_dvd (by decide) hk hv he hB hnd).1
  omega

omit [DecidableEq X] in
theorem lower_bound {C : Family X} (hk : 8 ≤ k) (hv : Fintype.card X = 4*k)
    (hC : IsCover C k 2) : (if 4 ∣ k then 20 else 21) ≤ C.card := by
  classical
  have h := (Multicover.ofFamily_isCover_one C k 2).mpr hC
  split_ifs with hd
  · simpa using indexed_twenty (by omega : 4 ≤ k) hv h
  · simpa using indexed_twenty_one (by omega : 4 ≤ k) hv h hd

end CoveringDesigns.C4k_K_2
