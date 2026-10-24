import CoveringDesigns.TwoKMinusC.OffsetTwo

/-! Specialisation of the preserved unconditional offset-two lower theorem.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns

/-- Every ordinary (34,18,3) cover has at least thirteen distinct blocks. -/
theorem lower_bound_34_18_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 34) (hC : IsCover C 18 3) : 13 ≤ C.card := by
  exact TwoKMinusC.OffsetTwo.thirteen_le_card (by omega) (by decide) hC

end CoveringDesigns
