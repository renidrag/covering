import CoveringDesigns.Schoenheim.LowerBound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Schönheim arithmetic for the even-group quadruple construction.
Classical lower bound; formalisation: Rob Gardiner, with AI assistance. -/

namespace CoveringDesigns.QuadrupleAssembly

private theorem ceil_product (a b : ℕ) (hb : 0 < b) :
    Schoenheim.ceilDiv (b*a) b = a := by
  apply Nat.le_antisymm
  · exact (Schoenheim.ceilDiv_le_iff hb).2 (by omega)
  · have h := (Schoenheim.ceilDiv_le_iff hb).1
      (le_refl (Schoenheim.ceilDiv (b*a) b))
    exact Nat.le_of_mul_le_mul_left h hb

/-- Every intermediate ceiling, with no rounding suppressed. -/
theorem ceilings {u : ℕ} (hu : 3 ≤ u) :
    Schoenheim.ceilDiv (12*u-1) 2 = 6*u ∧
    Schoenheim.ceilDiv (12*u*(6*u)) 3 = 24*u^2 ∧
    Schoenheim.ceilDiv ((12*u+1)*(24*u^2)) 4 = 6*u^2*(12*u+1) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Schoenheim.ceilDiv
    omega
  · rw [show 12*u*(6*u) = 3*(24*u^2) by ring]
    exact ceil_product _ _ (by decide)
  · rw [show (12*u+1)*(24*u^2) = 4*(6*u^2*(12*u+1)) by ring]
    exact ceil_product _ _ (by decide)

theorem schoenheim_evaluation {u : ℕ} (hu : 3 ≤ u) :
    Schoenheim.bound (12*u+1) 4 3 = 6*u^2*(12*u+1) := by
  have hs : 12*u+1-1 = 12*u := by omega
  norm_num only [Schoenheim.bound, Nat.reduceSub, Nat.mul_one]
  rw [hs, (ceilings hu).1, (ceilings hu).2.1, (ceilings hu).2.2]

/-- Universal lower bound on arbitrary finite labels, independent of all seeds. -/
theorem lower_bound {α : Type*} [Fintype α] [DecidableEq α]
    {u : ℕ} (hu : 3 ≤ u) (hv : Fintype.card α = 12*u+1)
    {C : Family α} (hC : IsCover C 4 3) : 6*u^2*(12*u+1) ≤ C.card := by
  have hk : 4 ≤ Fintype.card α := by rw [hv]; omega
  have h := Schoenheim.lower_bound (by decide : 1 ≤ 3) (by decide : 3 ≤ 4) hk hC
  simpa only [hv, schoenheim_evaluation hu] using h

end CoveringDesigns.QuadrupleAssembly
