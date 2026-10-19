import CoveringDesigns.TwoKMinusC.LargeDefect
import CoveringDesigns.TwoKMinusCGeneral.OffsetThreeArithmetic
import CoveringDesigns.TwoKMinusCGeneral.Saturation

/-! Sharper offset-three lower bound, using only conditional actual floors. -/
namespace CoveringDesigns.TwoKMinusCGeneral
variable {α : Type*} [Fintype α] {k : ℕ}

theorem fourteen_le_card_offset_three {C : Family α}
    (hv : Fintype.card α=2*k-3) (hk : 59≤k) (hC : IsCover C k 3) :
    14≤C.card := by
  classical
  have hv' : Fintype.card α+3=2*k := by omega
  by_contra hn
  have hb : C.card≤13 := by omega
  have hp (p q : α) (hpq : p≠q) : 3≤degree (star C p) q := by
    have htwo := pair_ge_two hv' (by decide) (by omega) hC hpq
    have hne := no_saturation_offset_three hv' (by omega) hC hb hpq
    omega
  have hr := TwoKMinusC.actual_floors_real hv' (by decide) (by omega) (by omega)
    hC.1 (degree_ge_six hv' (by decide) (by omega) hC) hp
  have ht := thirteen_lt_Q_three hk
  have hbR : (C.card : ℝ)≤13 := by exact_mod_cast hb
  linarith

end CoveringDesigns.TwoKMinusCGeneral
