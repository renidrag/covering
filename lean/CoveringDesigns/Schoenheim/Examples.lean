import CoveringDesigns.Schoenheim.LowerBound

/-! Numerical lower bounds from the general theorem, without result-specific imports. -/

namespace CoveringDesigns.Schoenheim

theorem bound_11_5_2 : bound 11 5 2 = 7 := rfl
theorem bound_12_6_3 : bound 12 6 3 = 14 := rfl
theorem bound_13_7_4 : bound 13 7 4 = 26 := rfl

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem lower_bound_11_5_2 {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) : 7 ≤ C.card := by
  have hb := lower_bound (by decide : 1 ≤ 2) (by decide : 2 ≤ 5) (by omega) h
  simpa only [hn, bound_11_5_2] using hb

theorem lower_bound_12_6_3 {C : Family α}
    (hn : Fintype.card α = 12) (h : IsCover C 6 3) : 14 ≤ C.card := by
  have hb := lower_bound (by decide : 1 ≤ 3) (by decide : 3 ≤ 6) (by omega) h
  simpa only [hn, bound_12_6_3] using hb

theorem lower_bound_13_7_4 {C : Family α}
    (hn : Fintype.card α = 13) (h : IsCover C 7 4) : 26 ≤ C.card := by
  have hb := lower_bound (by decide : 1 ≤ 4) (by decide : 4 ≤ 7) (by omega) h
  simpa only [hn, bound_13_7_4] using hb

end CoveringDesigns.Schoenheim
