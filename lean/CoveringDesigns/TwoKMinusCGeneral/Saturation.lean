import CoveringDesigns.TwoKMinusCGeneral.Capacity

/-! Saturation exclusions for hypothetical families of at most thirteen blocks. -/
namespace CoveringDesigns.TwoKMinusCGeneral
open Finset C20_11_3 TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α] {c k : ℕ}

theorem no_saturation_uniform {C : Family α} (hv : Fintype.card α+c=2*k)
    (hc : 2≤c) (hk : 25*c≤k) (hC : IsCover C k 3) (hb : C.card≤13)
    {p q : α} (hpq : p≠q) : degree (star C p) q≠2 := by
  intro hs
  have hcap := saturated_capacity hv hc (by omega) hC hpq hs
  have hpart := endpoint_card_partition C p q
  rw [hs] at hpart
  have hsum : (onlyBlocks C p q).card+(onlyBlocks C q p).card≤11 := by omega
  have hprod : (onlyBlocks C p q).card*(onlyBlocks C q p).card≤30 :=
    product_le_capacity hsum
  have hright := Nat.mul_le_mul_left (capacity c) hprod
  have hblocks := Nat.mul_le_mul_right (capacity k) (show C.card-2≤11 by omega)
  apply capacity_uniform_impossible hc hk
  calc
    _ ≤ 3*(k-c)*(k-c)+(k/2)*((onlyBlocks C p q).card+(onlyBlocks C q p).card) :=
      Nat.le_add_right _ _
    _ ≤ _ := hcap
    _ ≤ 11*capacity k+capacity c*30 :=
      add_le_add hblocks (by simpa [Nat.mul_assoc] using hright)
    _ = _ := by ring

theorem no_saturation_offset_three {C : Family α} (hv : Fintype.card α+3=2*k)
    (hk : 57≤k) (hC : IsCover C k 3) (hb : C.card≤13)
    {p q : α} (hpq : p≠q) : degree (star C p) q≠2 := by
  intro hs
  have hcap := saturated_capacity hv (by decide) (by omega) hC hpq hs
  have hp := onlyBlocks_card_add_pair C p q
  have hq := onlyBlocks_card_add_pair C q p
  rw [hs] at hp
  rw [pair_degree_comm C q p,hs] at hq
  have hdp := TwoKMinusCGeneral.degree_ge_six hv (by decide) (by omega) hC p
  have hdq := TwoKMinusCGeneral.degree_ge_six hv (by decide) (by omega) hC q
  have hpart := endpoint_card_partition C p q
  rw [hs] at hpart
  have hu : 4≤(onlyBlocks C p q).card := by omega
  have hw : 4≤(onlyBlocks C q p).card := by omega
  have hsum : (onlyBlocks C p q).card+(onlyBlocks C q p).card≤11 := by omega
  have he := endpoint_budget_three hu hw hsum (r := k/2) (by omega)
  have hblocks := Nat.mul_le_mul_right (capacity k) (show C.card-2≤11 by omega)
  rw [show capacity 3=2 from rfl] at hcap
  apply capacity_three_impossible hk
  omega

end CoveringDesigns.TwoKMinusCGeneral
