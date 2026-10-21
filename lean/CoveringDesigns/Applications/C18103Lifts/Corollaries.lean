import CoveringDesigns.Applications.C18103Lifts.LowerBound

/-! Five numerical consequences of one structural seed, not exactness claims. -/
namespace CoveringDesigns.Applications.C18103Lifts

/-- Ordinary kernel reduction checks the entire nested-ceiling sequence. -/
theorem ceilings :
    Multicover.bound 12 18 10 0 = 12 ∧
    Multicover.bound 12 19 11 1 = 21 ∧
    Multicover.bound 12 20 12 2 = 35 ∧
    Multicover.bound 12 21 13 3 = 57 ∧
    Multicover.bound 12 22 14 4 = 90 ∧
    Multicover.bound 12 23 15 5 = 138 := by decide

/-- C(19,11,4) ≥ 21 on arbitrary finite point types. -/
theorem lower_bound_19_11_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 19) (hC : IsCover C 11 4) : 21 ≤ C.card := by
  simpa only [ceilings.2.1] using lower_bound 1 hv hC

/-- C(20,12,5) ≥ 35 on arbitrary finite point types. -/
theorem lower_bound_20_12_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 20) (hC : IsCover C 12 5) : 35 ≤ C.card := by
  simpa only [ceilings.2.2.1] using lower_bound 2 hv hC

/-- C(21,13,6) ≥ 57 on arbitrary finite point types. -/
theorem lower_bound_21_13_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 21) (hC : IsCover C 13 6) : 57 ≤ C.card := by
  simpa only [ceilings.2.2.2.1] using lower_bound 3 hv hC

/-- C(22,14,7) ≥ 90 on arbitrary finite point types. -/
theorem lower_bound_22_14_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 22) (hC : IsCover C 14 7) : 90 ≤ C.card := by
  simpa only [ceilings.2.2.2.2.1] using lower_bound 4 hv hC

/-- C(23,15,8) ≥ 138 on arbitrary finite point types. -/
theorem lower_bound_23_15_8 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 23) (hC : IsCover C 15 8) : 138 ≤ C.card := by
  simpa only [ceilings.2.2.2.2.2] using lower_bound 5 hv hC

end CoveringDesigns.Applications.C18103Lifts
