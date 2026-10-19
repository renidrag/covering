import CoveringDesigns.HorsleySingh.LowerBound

/-! A consequence of Horsley–Singh Theorem 6, not an optimality claim. -/

namespace CoveringDesigns.HorsleySingh

universe u

theorem schoenheim_13_5_1 : Schoenheim.bound 13 5 1 = 3 := rfl
theorem schoenheim_14_6_2 : Schoenheim.bound 14 6 2 = 7 := rfl
theorem schoenheim_15_7_3 : Schoenheim.bound 15 7 3 = 15 := rfl
theorem schoenheim_17_9_5 : Schoenheim.bound 17 9 5 = 57 := rfl

theorem smaller_13_5_1 : CoverLower.{u} 13 5 1 3 := by
  rw [← schoenheim_13_5_1]
  exact schoenheim_coverLower (by decide) (by decide)

theorem smaller_14_6_2 : CoverLower.{u} 14 6 2 7 := by
  rw [← schoenheim_14_6_2]
  exact schoenheim_coverLower (by decide) (by decide)

theorem smaller_15_7_3 : CoverLower.{u} 15 7 3 15 := by
  rw [← schoenheim_15_7_3]
  exact schoenheim_coverLower (by decide) (by decide)

/-- Every numerical hypothesis of Lemma 3, including both ceilings. -/
theorem parameters_17_9_5 : Parameters 17 9 5 15 7 3 := by
  constructor <;> decide

theorem diagonal_17_9_5 : diagonal 15 7 3 = 4 := rfl
theorem defect_17_9_5 : defect 17 9 15 7 3 = 0 := rfl
theorem bound_17_9_5 : bound 17 9 15 = 59 := rfl

/-- A covering inequality for any finite point type and any covering family. -/
theorem lower_bound_17_9_5 {α : Type u} [Fintype α] [DecidableEq α]
    {C : Family α} (hn : Fintype.card α = 17) (h : IsCover C 9 5) :
    59 ≤ C.card := by
  rw [← bound_17_9_5]
  exact lower_bound parameters_17_9_5 smaller_15_7_3 smaller_14_6_2 smaller_13_5_1
    hn h (by rw [defect_17_9_5, diagonal_17_9_5]; decide)

end CoveringDesigns.HorsleySingh
