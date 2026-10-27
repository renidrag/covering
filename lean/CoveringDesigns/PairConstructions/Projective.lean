import CoveringDesigns.ProjectiveHyperplanes.Geometry
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The line-intersection fact needed for weighted projective pair coverings. -/
namespace CoveringDesigns.PairConstructions
open Finset Module ProjectiveHyperplanes
variable {F : Type*} [Field F] [Fintype F]

/-- Distinct lines in the existing projective plane meet in exactly one point. -/
theorem projective_line_intersection [DecidableEq (Point F 3)] (d e : Direction F 3) (hne : d ≠ e) :
    (hyperplane d ∩ hyperplane e).card = 1 := by
  classical
  let S := LinearMap.ker d.rep
  let T := LinearMap.ker e.rep
  have hs : finrank F S = 2 := kernel_finrank d
  have ht : finrank F T = 2 := kernel_finrank e
  have hle : finrank F (S ⊓ T : Submodule F (Fin 3 → F)) ≤ 2 := by
    simpa [hs] using (Submodule.finrank_mono (inf_le_left : S ⊓ T ≤ S))
  have hn : finrank F (S ⊓ T : Submodule F (Fin 3 → F)) ≠ 2 := by
    intro hh
    have hS : S ⊓ T = S := Submodule.eq_of_le_of_finrank_eq inf_le_left (hh.trans hs.symm)
    have hT : S ⊓ T = T := Submodule.eq_of_le_of_finrank_eq inf_le_right (hh.trans ht.symm)
    exact hne (dual_eq_of_kernel_eq d e (hS.symm.trans hT))
  have hd := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hu : finrank F (S ⊔ T : Submodule F (Fin 3 → F)) ≤ 3 := by
    simpa using (S ⊔ T).finrank_le
  have hi : finrank F (S ⊓ T : Submodule F (Fin 3 → F)) = 1 := by omega
  have hp : hyperplane d ∩ hyperplane e = points (S ⊓ T) := by
    ext p
    simp [hyperplane,mem_points,LiesIn,le_inf_iff,S,T]
  rw [hp,points_card,hi]
  simp [G,AffineSchoenheim.geom]

end CoveringDesigns.PairConstructions
