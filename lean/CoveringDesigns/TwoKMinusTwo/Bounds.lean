import CoveringDesigns.TwoKMinusTwo.Rank
import CoveringDesigns.TwoKMinusTwo.Capacity

/-! Universal lower bounds; all structural hypotheses are derived internally. -/
namespace CoveringDesigns.TwoKMinusTwo
open Finset C20_11_3
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

theorem saturated_capacity_reduced {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k) (hC : IsCover C k 3)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2)
    (hr : C.card-6 ≤ k/2) :
    3*(k-2)*(k-2)+8*(k/2) ≤ (C.card-2)*capacity k+16 := by
  have hc := saturated_capacity hv (by omega) hC hpq hsat
  have hp := onlyBlocks_card_add_pair C p q
  have hq := onlyBlocks_card_add_pair C q p
  rw [hsat] at hp
  rw [pair_degree_comm C q p,hsat] at hq
  have hdp := degree_ge_six hv hk hC p
  have hdq := degree_ge_six hv hk hC q
  have hpart := endpoint_card_partition C p q
  rw [hsat] at hpart
  have hu : 4 ≤ (onlyBlocks C p q).card := by omega
  have hw : 4 ≤ (onlyBlocks C q p).card := by omega
  have hur : (onlyBlocks C p q).card ≤ k/2 := by omega
  have hwr : (onlyBlocks C q p).card ≤ k/2 := by omega
  have hb := endpoint_budget hu hw hur hwr
  omega

theorem no_saturation_twelve {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 17 ≤ k) (hC : IsCover C k 3)
    (hb : C.card ≤ 12) {p q : α} (hpq : p ≠ q) :
    degree (star C p) q ≠ 2 := by
  intro hs
  have hc := saturated_capacity_reduced hv (by omega) hC hpq hs (by omega)
  have hm := Nat.mul_le_mul_right (capacity k) (show C.card-2 ≤ 10 by omega)
  exact capacity_twelve_impossible hk (by omega)

theorem no_saturation_thirteen {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k) (hC : IsCover C k 3)
    (hb : C.card ≤ 13) {p q : α} (hpq : p ≠ q) :
    degree (star C p) q ≠ 2 := by
  intro hs
  have hc := saturated_capacity_reduced hv (by omega) hC hpq hs (by omega)
  have hm := Nat.mul_le_mul_right (capacity k) (show C.card-2 ≤ 11 by omega)
  exact capacity_thirteen_impossible hk (by omega)

theorem thirteen_le_card {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 20 ≤ k) (hC : IsCover C k 3) :
    13 ≤ C.card := by
  by_contra hn
  have hb : C.card ≤ 12 := by omega
  have hp (p q : α) (hpq : p ≠ q) : 3 ≤ degree (star C p) q := by
    have htwo := pair_ge_two hv (by omega) hC hpq
    have hne := no_saturation_twelve hv (by omega) hC hb hpq
    omega
  have hr := conditional_rank hv (by omega) hC hp
  have hm := Nat.mul_le_mul_left (k+2) hb
  have hs : k-1+1=k := by omega
  nlinarith

theorem fourteen_le_card {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 41 ≤ k) (hC : IsCover C k 3) :
    14 ≤ C.card := by
  by_contra hn
  have hb : C.card ≤ 13 := by omega
  have hp (p q : α) (hpq : p ≠ q) : 3 ≤ degree (star C p) q := by
    have htwo := pair_ge_two hv (by omega) hC hpq
    have hne := no_saturation_thirteen hv (by omega) hC hb hpq
    omega
  have hr := conditional_rank hv (by omega) hC hp
  have hm := Nat.mul_le_mul_left (k+2) hb
  have hs : k-1+1=k := by omega
  nlinarith

/-- The proposed inequality holds unconditionally for every k≥9. -/
theorem lower_inequality {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k) (hC : IsCover C k 3) :
    14*(k-1) ≤ (k+2)*C.card := by
  have hi := incidence_lower_bound hC.1 (degree_ge_six hv hk hC)
  rw [hv] at hi
  have hs : k-1+1=k := by omega
  have ht : 2*k-2+2=2*k := by omega
  have h11 : 11 ≤ C.card := by
    by_contra hn
    have hm := Nat.mul_le_mul_left k (show C.card ≤ 10 by omega)
    nlinarith
  by_cases h12 : k ≤ 12
  · have hm := Nat.mul_le_mul_left (k+2) h11
    nlinarith
  have h12b : 12 ≤ C.card := by
    by_contra hn
    have hm := Nat.mul_le_mul_left k (show C.card ≤ 11 by omega)
    nlinarith
  by_cases h19 : k ≤ 19
  · have hm := Nat.mul_le_mul_left (k+2) h12b
    nlinarith
  have h13b := thirteen_le_card hv (by omega) hC
  by_cases h40 : k ≤ 40
  · have hm := Nat.mul_le_mul_left (k+2) h13b
    nlinarith
  have h14b := fourteen_le_card hv (by omega) hC
  have hm := Nat.mul_le_mul_left (k+2) h14b
  nlinarith

end CoveringDesigns.TwoKMinusTwo
