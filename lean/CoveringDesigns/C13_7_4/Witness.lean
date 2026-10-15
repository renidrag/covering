import CoveringDesigns.Foundations.Basic

/- Generated from the retained JSON data. These are exact finite witnesses;
the generator supplies data, not proof assumptions. All checks use the kernel.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns


def knownCover30 : Family (Fin 13) :=
{
  {0, 1, 4, 5, 6, 7, 8},
  {0, 2, 3, 4, 5, 7, 9},
  {1, 2, 5, 6, 7, 8, 9},
  {1, 2, 3, 4, 7, 8, 10},
  {0, 2, 4, 6, 7, 9, 10},
  {0, 1, 3, 7, 8, 9, 10},
  {0, 1, 2, 4, 6, 9, 11},
  {0, 2, 3, 4, 8, 9, 11},
  {0, 1, 3, 4, 5, 10, 11},
  {0, 2, 5, 6, 8, 10, 11},
  {1, 5, 6, 7, 8, 10, 11},
  {3, 5, 6, 7, 8, 10, 11},
  {1, 2, 3, 5, 9, 10, 11},
  {4, 5, 6, 8, 9, 10, 11},
  {2, 3, 4, 5, 6, 8, 12},
  {0, 1, 2, 4, 5, 9, 12},
  {0, 3, 5, 6, 8, 9, 12},
  {0, 1, 2, 3, 6, 10, 12},
  {1, 3, 6, 7, 8, 10, 12},
  {1, 3, 4, 6, 9, 10, 12},
  {0, 2, 4, 8, 9, 10, 12},
  {0, 3, 4, 6, 7, 11, 12},
  {1, 3, 5, 6, 7, 11, 12},
  {0, 1, 2, 7, 8, 11, 12},
  {2, 3, 6, 7, 9, 11, 12},
  {1, 4, 7, 8, 9, 11, 12},
  {2, 4, 5, 7, 10, 11, 12},
  {1, 3, 5, 8, 10, 11, 12},
  {5, 6, 7, 8, 10, 11, 12},
  {0, 5, 7, 9, 10, 11, 12}
}

theorem knownCover30_card : knownCover30.card = 30 := by decide +kernel

#print axioms knownCover30_card

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover30_uniform : Uniform knownCover30 7 := by
  unfold Uniform knownCover30
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem knownCover30_covers : Covers knownCover30 4 := by
  apply covers_of_powersetCard
  unfold knownCover30
  decide +kernel

theorem upper_bound_30 : ∃ C : Family (Fin 13), IsCover C 7 4 ∧ C.card = 30 :=
  ⟨knownCover30, ⟨knownCover30_uniform, knownCover30_covers⟩, knownCover30_card⟩

#print axioms upper_bound_30

end CoveringDesigns
