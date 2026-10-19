import CoveringDesigns.TwoKMinusCGeneral.Rank
import CoveringDesigns.TwoKMinusCGeneral.Saturation

/-! Uniform-offset lower bound via partitioned strict rank, without the
large-defect adapter. -/
namespace CoveringDesigns.TwoKMinusCGeneral
variable {α : Type*} [Fintype α] {c k : ℕ}

theorem fourteen_le_card_uniform {C : Family α}
    (hv : Fintype.card α=2*k-c) (hc : 2≤c) (hk : 25*c≤k) (hC : IsCover C k 3) :
    14≤C.card := by
  classical
  have hv' : Fintype.card α+c=2*k := by omega
  by_contra hn
  have hb : C.card≤13 := by omega
  have hp (p q : α) (hpq : p≠q) : 3≤degree (star C p) q := by
    have htwo := pair_ge_two hv' hc (by omega) hC hpq
    have hne := no_saturation_uniform hv' hc hk hC hb hpq
    omega
  have hr := conditional_rank hv' hc hC.1 (degree_ge_six hv' hc (by omega) hC) hp
  have hm := Nat.mul_le_mul_left (k+c) hb
  nlinarith

end CoveringDesigns.TwoKMinusCGeneral
