import CoveringDesigns.TwoKMinusTwoTightening.Endpoints
import CoveringDesigns.TwoKMinusC.OffsetTwo

/-! Additive checkpoint refinements, preserving the existing family proofs.
Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusTwoTightening

variable {α : Type*} [Fintype α] {k : ℕ}

/-- The new lower endpoint, with every structural premise derived internally. -/
theorem lower_bound_32_17_3 {C : Family α} (hv : Fintype.card α = 32)
    (hC : IsCover C 17 3) : 13 ≤ C.card := by
  classical
  by_contra hn
  have hb : C.card ≤ 12 := by omega
  have hl := TwoKMinusTwo.lower_inequality (k := 17) (by omega) (by norm_num) hC
  have heq : C.card = 12 := by omega
  have hp (x y : α) (hxy : x ≠ y) : 3 ≤ degree (star C x) y := by
    have htwo := TwoKMinusTwo.pair_ge_two (k := 17) (by omega) (by norm_num) hC hxy
    have hne := TwoKMinusTwo.no_saturation_twelve (k := 17)
      (by omega) (by norm_num) hC hb hxy
    omega
  exact no_twelve_32_17 hv hC.1 heq
    (TwoKMinusTwo.degree_ge_six (k := 17) (by omega) (by norm_num) hC) hp

/-- The new exactness endpoint, independent of any component classification. -/
theorem lower_bound_68_35_3 {C : Family α} (hv : Fintype.card α = 68)
    (hC : IsCover C 35 3) : 14 ≤ C.card := by
  classical
  by_contra hn
  have hb : C.card ≤ 13 := by omega
  have hl := TwoKMinusC.OffsetTwo.thirteen_le_card (k := 35)
    (by omega) (by norm_num) hC
  have heq : C.card = 13 := by omega
  have hp (x y : α) (hxy : x ≠ y) : 3 ≤ degree (star C x) y := by
    have htwo := TwoKMinusTwo.pair_ge_two (k := 35) (by omega) (by norm_num) hC hxy
    have hne := TwoKMinusTwo.no_saturation_thirteen (k := 35)
      (by omega) (by norm_num) hC hb hxy
    omega
  exact no_thirteen_68_35 hv hC.1 heq
    (TwoKMinusTwo.degree_ge_six (k := 35) (by omega) (by norm_num) hC) hp

/-- At least thirteen blocks for every k≥17. -/
theorem thirteen_le_card {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 17 ≤ k) (hC : IsCover C k 3) : 13 ≤ C.card := by
  by_cases h18 : 18 ≤ k
  · exact TwoKMinusC.OffsetTwo.thirteen_le_card hv h18 hC
  · have heq : k = 17 := by omega
    subst k
    exact lower_bound_32_17_3 (by omega) hC

/-- At least fourteen blocks for every k≥35. -/
theorem fourteen_le_card {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 35 ≤ k) (hC : IsCover C k 3) : 14 ≤ C.card := by
  by_cases h36 : 36 ≤ k
  · exact TwoKMinusC.OffsetTwo.fourteen_le_card hv h36 hC
  · have heq : k = 35 := by omega
    subst k
    exact lower_bound_68_35_3 (by omega) hC

/-- Both halves of exactness, including an actual attaining ordinary family. -/
theorem exactness (hv : Fintype.card α = 2*k-2) (hk : 35 ≤ k) :
    (∃ C : Family α, IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C k 3 → 14 ≤ C.card) := by
  obtain ⟨C,hC,hcard⟩ := TwoKMinusTwo.upper_bound hv (by omega : 3 ≤ k)
  exact ⟨⟨C,hC,Nat.le_antisymm hcard (fourteen_le_card hv hk hC)⟩,
    fun _ h => fourteen_le_card hv hk h⟩

theorem covering_number (hk : 35 ≤ k) :
    (∃ C : Family (Fin (2*k-2)), IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin (2*k-2)), IsCover C k 3 → 14 ≤ C.card) :=
  exactness (by simp) hk

theorem interval_32_17_3_on (hv : Fintype.card α = 32) :
    (∃ C : Family α, IsCover C 17 3 ∧ C.card ≤ 14) ∧
    (∀ C : Family α, IsCover C 17 3 → 13 ≤ C.card) :=
  ⟨TwoKMinusTwo.upper_bound (k := 17) (by omega) (by norm_num),
    fun _ h => lower_bound_32_17_3 hv h⟩

theorem exactness_68_35_3_on (hv : Fintype.card α = 68) :
    (∃ C : Family α, IsCover C 35 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C 35 3 → 14 ≤ C.card) :=
  exactness (k := 35) (by omega) (by norm_num)

end CoveringDesigns.TwoKMinusTwoTightening
