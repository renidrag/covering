import CoveringDesigns.Qk_K_2.Exact
import CoveringDesigns.Qk_K_2.NumericalLower
import CoveringDesigns.Qk_K_2.Perona
import CoveringDesigns.Qk_K_2.DeHeerMuir

namespace CoveringDesigns.Qk_K_2

private theorem five_prime_power : IsPrimePow 5 := (by decide : Nat.Prime 5).isPrimePow
private theorem seven_prime_power : IsPrimePow 7 := (by decide : Nat.Prime 7).isPrimePow
private theorem nine_prime_power : IsPrimePow 9 := by
  exact (isPrimePow_nat_iff 9).mpr ⟨3,2,by decide,by decide,by decide⟩

theorem exact_55_11_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 55) :
    (∃ C : Family α, IsCover C 11 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 11 2 → 31 ≤ C.card) := by
  exact weighted_endpoint_divisibility (q := 5) (u := 2) (r := 1)
    five_prime_power (by decide) (by decide) (by decide) (by decide) hv (by decide)

theorem attainment_55_11_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 55) :
    ∃ C : Family α, IsCover C 11 2 ∧ C.card = 31 := (exact_55_11_2 hv).1

theorem covering_number_55_11_2 :
    (∃ C : Family (Fin 55), IsCover C 11 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 55), IsCover C 11 2 → 31 ≤ C.card) := exact_55_11_2 (by simp)

theorem exact_65_13_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 65) :
    (∃ C : Family α, IsCover C 13 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 13 2 → 31 ≤ C.card) := by
  exact ⟨Perona.attainment hv,fun _ hC => lower_bound_65_13_2 hv hC⟩

theorem attainment_65_13_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 65) :
    ∃ C : Family α, IsCover C 13 2 ∧ C.card = 31 := (exact_65_13_2 hv).1

theorem covering_number_65_13_2 :
    (∃ C : Family (Fin 65), IsCover C 13 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 65), IsCover C 13 2 → 31 ≤ C.card) := exact_65_13_2 (by simp)

theorem exact_80_16_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 80) :
    (∃ C : Family α, IsCover C 16 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 16 2 → 31 ≤ C.card) := by
  exact weighted_endpoint_divisibility (q := 5) (u := 3) (r := 1)
    five_prime_power (by decide) (by decide) (by decide) (by decide) hv (by decide)

theorem attainment_80_16_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 80) :
    ∃ C : Family α, IsCover C 16 2 ∧ C.card = 31 := (exact_80_16_2 hv).1

theorem covering_number_80_16_2 :
    (∃ C : Family (Fin 80), IsCover C 16 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 80), IsCover C 16 2 → 31 ≤ C.card) := exact_80_16_2 (by simp)

theorem exact_85_17_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 85) :
    (∃ C : Family α, IsCover C 17 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 17 2 → 31 ≤ C.card) := by
  exact weighted_endpoint_divisibility (q := 5) (u := 3) (r := 2)
    five_prime_power (by decide) (by decide) (by decide) (by decide) hv (by decide)

theorem attainment_85_17_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 85) :
    ∃ C : Family α, IsCover C 17 2 ∧ C.card = 31 := (exact_85_17_2 hv).1

theorem covering_number_85_17_2 :
    (∃ C : Family (Fin 85), IsCover C 17 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 85), IsCover C 17 2 → 31 ≤ C.card) := exact_85_17_2 (by simp)

theorem exact_95_19_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 95) :
    (∃ C : Family α, IsCover C 19 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 19 2 → 31 ≤ C.card) := by
  exact ⟨DeHeerMuir.attainment hv,fun _ hC => lower_bound_95_19_2 hv hC⟩

theorem attainment_95_19_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 95) :
    ∃ C : Family α, IsCover C 19 2 ∧ C.card = 31 := (exact_95_19_2 hv).1

theorem covering_number_95_19_2 :
    (∃ C : Family (Fin 95), IsCover C 19 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 95), IsCover C 19 2 → 31 ≤ C.card) := exact_95_19_2 (by simp)

theorem exact_56_8_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 56) :
    (∃ C : Family α, IsCover C 8 2 ∧ C.card = 57) ∧
      (∀ C : Family α, IsCover C 8 2 → 57 ≤ C.card) := by
  exact weighted_endpoint_exclusion (q := 7) (a := 1) (r := 1)
    seven_prime_power (by decide) (by decide) (by decide) (by decide) hv no_twisted_seven

theorem attainment_56_8_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 56) :
    ∃ C : Family α, IsCover C 8 2 ∧ C.card = 57 := (exact_56_8_2 hv).1

theorem covering_number_56_8_2 :
    (∃ C : Family (Fin 56), IsCover C 8 2 ∧ C.card = 57) ∧
      (∀ C : Family (Fin 56), IsCover C 8 2 → 57 ≤ C.card) := exact_56_8_2 (by simp)

theorem exact_90_10_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 90) :
    (∃ C : Family α, IsCover C 10 2 ∧ C.card = 91) ∧
      (∀ C : Family α, IsCover C 10 2 → 91 ≤ C.card) := by
  exact weighted_endpoint_exclusion (q := 9) (a := 1) (r := 1)
    nine_prime_power (by decide) (by decide) (by decide) (by decide) hv no_twisted_nine

theorem attainment_90_10_2 {α : Type*} [Fintype α] (hv : Fintype.card α = 90) :
    ∃ C : Family α, IsCover C 10 2 ∧ C.card = 91 := (exact_90_10_2 hv).1

theorem covering_number_90_10_2 :
    (∃ C : Family (Fin 90), IsCover C 10 2 ∧ C.card = 91) ∧
      (∀ C : Family (Fin 90), IsCover C 10 2 → 91 ≤ C.card) := exact_90_10_2 (by simp)

end CoveringDesigns.Qk_K_2
