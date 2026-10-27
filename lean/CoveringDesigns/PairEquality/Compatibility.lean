import CoveringDesigns.PairEquality.Classification
import CoveringDesigns.TruncatedPlaneLoads.Family

/-! Compatibility uses the original positive weights and the entire family. -/

namespace CoveringDesigns.PairEquality
open Finset
variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

theorem admissible_of_core {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ}
    (h : PositiveUnitLoads q H w) (P : TruncatedPlaneLoads.Plane q I G)
    (hc : P.core ⊆ H) : TruncatedPlaneLoads.Admissible P H w 1 :=
  ⟨hc,h.uniform,fun _ hE _ hF => h.meets hE hF,h.positive,h.load,by norm_num⟩

/-- The same dichotomy with the unchanged load-classification hypotheses
already supplied on the core branch. The coefficient function is the original w. -/
theorem admissible_or_twisted {q : ℕ} (hq : 4 ≤ q)
    {H : Finset (Finset I)} {w : Finset I → ℝ} (h : PositiveUnitLoads q H w) :
    (∃ P : TruncatedPlaneLoads.Plane q I (Fin (q+1)),
      TruncatedPlaneLoads.Admissible P H w 1) ∨ IsTwistedPlane q H := by
  rcases geometric_dichotomy hq h with ⟨P,hP⟩ | hT
  · exact Or.inl ⟨P,admissible_of_core h P hP⟩
  · exact Or.inr hT

end CoveringDesigns.PairEquality
