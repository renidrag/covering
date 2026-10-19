import CoveringDesigns.TwoKMinusTwoEquality.Rigidity
import CoveringDesigns.TwoKMinusTwo.Bounds

/-! Equality endpoint exclusions; existing family theorems remain unchanged.
Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusTwoEquality
open Finset TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

/-- Equality in the unrounded incidence/rank inequality forces twice as many
low points as actual blocks. -/
theorem low_count_eq_of_tight {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k) (hC : IsCover C k 3)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (htight : 14*(k-1) = (k+2)*C.card) :
    (minimumPoints C 6).card = 2*C.card := by
  have hr := low_card_le hv (by omega) hC.1 hpair
  have hi := minimum_points_bound hC.1 (degree_ge_six hv hk hC)
  rw [hv] at hi
  have hsub : k-1+1=k := by omega
  have hsub2 : 2*k-2+2=2*k := by omega
  nlinarith

/-- Conditional equality can only have the eleven-block budget. -/
theorem card_eleven_of_tight {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k) (hC : IsCover C k 3)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (htight : 14*(k-1) = (k+2)*C.card) : C.card = 11 :=
  card_eleven_of_low_equality hv (by omega) hC.1 hpair
    (low_count_eq_of_tight hv hk hC hpair htight)

/-- The first reviewed endpoint: no twelve-block cover on 36 points. -/
theorem lower_bound_36_19_3 {C : Family α}
    (hv : Fintype.card α = 36) (hC : IsCover C 19 3) : 13 ≤ C.card := by
  have hv' : Fintype.card α = 2*19-2 := by omega
  by_contra hbad
  have hb : C.card ≤ 12 := by omega
  have hi := TwoKMinusTwo.lower_inequality hv' (by norm_num) hC
  have hc : C.card = 12 := by norm_num at hi; omega
  have hp : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y := by
    intro x y hxy
    have htwo := TwoKMinusTwo.pair_ge_two hv' (by norm_num) hC hxy
    have hne := TwoKMinusTwo.no_saturation_twelve hv' (by norm_num) hC hb hxy
    omega
  have he := card_eleven_of_tight hv' (by norm_num) hC hp (by norm_num [hc])
  omega

/-- The second reviewed endpoint: no thirteen-block cover on 78 points. -/
theorem lower_bound_78_40_3 {C : Family α}
    (hv : Fintype.card α = 78) (hC : IsCover C 40 3) : 14 ≤ C.card := by
  have hv' : Fintype.card α = 2*40-2 := by omega
  by_contra hbad
  have hb : C.card ≤ 13 := by omega
  have hi := TwoKMinusTwo.lower_inequality hv' (by norm_num) hC
  have hc : C.card = 13 := by norm_num at hi; omega
  have hp : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y := by
    intro x y hxy
    have htwo := TwoKMinusTwo.pair_ge_two hv' (by norm_num) hC hxy
    have hne := TwoKMinusTwo.no_saturation_thirteen hv' (by norm_num) hC hb hxy
    omega
  have he := card_eleven_of_tight hv' (by norm_num) hC hp (by norm_num [hc])
  omega

/-- New wrapper: the lower thirteen threshold starts at k=19. -/
theorem thirteen_le_card {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 19 ≤ k)
    (hC : IsCover C k 3) : 13 ≤ C.card := by
  by_cases he : k=19
  · subst k
    exact lower_bound_36_19_3 (by omega) hC
  · exact TwoKMinusTwo.thirteen_le_card hv (by omega) hC

/-- New wrapper: the lower fourteen threshold starts at k=40. -/
theorem fourteen_le_card {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 40 ≤ k)
    (hC : IsCover C k 3) : 14 ≤ C.card := by
  by_cases he : k=40
  · subst k
    exact lower_bound_78_40_3 (by omega) hC
  · exact TwoKMinusTwo.fourteen_le_card hv (by omega) hC

end CoveringDesigns.TwoKMinusTwoEquality
