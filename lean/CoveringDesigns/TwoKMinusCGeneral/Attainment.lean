import CoveringDesigns.TwoKMinusTwo.Construction
import CoveringDesigns.PointReduction.Family

/-! Arbitrary-label upper witnesses by ordinary-family reduction and padding. -/
namespace CoveringDesigns.TwoKMinusCGeneral
variable {α : Type*} [Fintype α] {c k : ℕ}

theorem upper_bound (hv : Fintype.card α+c=2*k) (hc : 2≤c) (hck : c≤k) (hk : 3≤k) :
    ∃ C : Family α, IsCover C k 3 ∧ C.card≤14 := by
  classical
  obtain ⟨C,hC,hb⟩ := TwoKMinusTwo.upper_bound (α := Fin (2*k-2)) (by simp) hk
  obtain ⟨D,hD,hd⟩ := PointReduction.family_reduce_points (β := α) hC
    (by omega) (by simp only [Fintype.card_fin]; omega)
  exact ⟨D,hD,hd.trans hb⟩

end CoveringDesigns.TwoKMinusCGeneral
