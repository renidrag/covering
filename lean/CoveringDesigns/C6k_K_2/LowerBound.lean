import CoveringDesigns.C6k_K_2.Matrix
import CoveringDesigns.C6k_K_2.Completion
import CoveringDesigns.PairDivisibility.Adapter
import CoveringDesigns.PairConsequences.Arithmetic

/-! The unrestricted lower bound, including repeated block occurrences. -/

namespace CoveringDesigns.C6k_K_2

/-- Completion on the actual supports excludes every order-six truncated core. -/
theorem no_plane_six {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)) : False :=
  no_order_six_matrix (completed_lines_card P) (completed_points_card P)
    (completedIncidence P) (completed_row_sum P) (completed_row_gram P)
    (completed_column_gram P)

/-- Every pair covering on `6k` points by `k`-block occurrences needs at
least 43 occurrences when `k ≥ 6`; repeated block images are allowed. -/
theorem indexed_lower_bound {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {k : ℕ} {B : I → Finset X}
    (hk : 6 ≤ k) (hv : Fintype.card X = 6*k)
    (hB : Multicover.IsCover B k 2 1) : 43 ≤ Fintype.card I := by
  have hf := PairDivisibility.incidence_floor (by decide : 4 ≤ 6) hk hv hB
  by_contra h
  have hi : Fintype.card I = 6*(6+1) := by omega
  rcases PairEquality.geometric_dichotomy (by decide : 4 ≤ 6)
    (PairDivisibility.normalized_loads (by decide) hk hv hi hB) with ⟨P, _⟩ | T
  · exact no_plane_six P
  · exact PairConsequences.no_twisted_six T

/-- `C(6k,k,2) ≥ 43` for every `k ≥ 6`, on arbitrary finite point labels. -/
theorem lower_bound {X : Type*} [Fintype X] {C : Family X} {k : ℕ}
    (hk : 6 ≤ k) (hv : Fintype.card X = 6*k) (hC : IsCover C k 2) : 43 ≤ C.card := by
  classical
  simpa using indexed_lower_bound hk hv ((Multicover.ofFamily_isCover_one C k 2).mpr hC)

end CoveringDesigns.C6k_K_2
