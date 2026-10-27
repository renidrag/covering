import CoveringDesigns.PairEquality.Extraction
import CoveringDesigns.PairEquality.Core
import CoveringDesigns.PairEquality.Twisted

/-! The geometric equality dichotomy on the original coordinates and supports. -/

namespace CoveringDesigns.PairEquality
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Füredi's geometric equality classification, specialised to positive unit
loads on exactly q(q+1) coordinates. In the first branch only the occupied
core is selected; the original weights and all extra supports remain present.
In the second branch maximality restores the entire original family. -/
theorem geometric_dichotomy {q : ℕ} (hq : 4 ≤ q)
    {H : Finset (Finset I)} {w : Finset I → ℝ} (h : PositiveUnitLoads q H w) :
    (∃ P : TruncatedPlaneLoads.Plane q I (Fin (q+1)), P.core ⊆ H) ∨
      IsTwistedPlane q H := by
  obtain ⟨J,hJ,a,ha,hli,_⟩ := independent_subfamily (by omega : 0 < q) h
  by_cases hx : ∃ x, degree J x = q
  · obtain ⟨P,hP⟩ := plane_of_degree_q (by omega) ha hli hx
    exact Or.inl ⟨P,hP ▸ hJ⟩
  · have T : IsTwistedPlane q J := twisted_of_no_degree_q ha hli (by simpa using hx)
    have heq : H = J := Subset.antisymm (by
      intro E hE
      apply T.maximal hq (h.uniform E hE)
      intro F hF
      exact h.meets hE (hJ hF)) hJ
    exact Or.inr (heq ▸ T)

end CoveringDesigns.PairEquality
