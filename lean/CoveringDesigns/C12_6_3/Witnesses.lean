import CoveringDesigns.Foundations.Basic

/- Generated from the retained JSON data. These are exact finite witnesses;
the generator supplies data, not proof assumptions. All checks use the kernel.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace CoveringDesigns


def figure1 : Family (Fin 12) :=
{
  {0, 1, 4, 5, 8, 9},
  {0, 2, 4, 6, 8, 10},
  {0, 3, 4, 7, 8, 11},
  {0, 1, 6, 7, 10, 11},
  {0, 2, 5, 7, 9, 11},
  {0, 3, 5, 6, 9, 10},
  {2, 3, 4, 5, 10, 11},
  {1, 3, 4, 6, 9, 11},
  {1, 2, 4, 7, 9, 10},
  {2, 3, 6, 7, 8, 9},
  {1, 3, 5, 7, 8, 10},
  {1, 2, 5, 6, 8, 11},
  {0, 1, 2, 3},
  {4, 5, 6, 7},
  {8, 9, 10, 11}
}

theorem figure1_card : figure1.card = 15 := by decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem figure1_covers : Covers figure1 3 := by
  apply covers_of_powersetCard
  unfold figure1
  decide +kernel

def figure6 : Family (Fin 12) :=
{
  {0, 1, 2, 3, 4, 5},
  {0, 1, 2, 6, 7, 8},
  {0, 1, 2, 9, 10, 11},
  {0, 3, 7, 8, 10, 11},
  {0, 4, 5, 6, 10, 11},
  {0, 4, 5, 7, 8, 9},
  {0, 3, 4, 5, 6, 9},
  {1, 3, 6, 8, 9, 11},
  {1, 4, 5, 7, 9, 11},
  {1, 4, 5, 6, 8, 10},
  {1, 3, 4, 5, 7, 10},
  {2, 3, 6, 7, 9, 10},
  {2, 4, 5, 8, 9, 10},
  {2, 4, 5, 6, 7, 11},
  {2, 3, 4, 5, 8, 11}
}

theorem figure6_card : figure6.card = 15 := by decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem figure6_isCover : IsCover figure6 6 3 := by
  constructor
  · unfold Uniform figure6
    decide +kernel
  · apply covers_of_powersetCard
    unfold figure6
    decide +kernel

#print axioms figure1_covers
#print axioms figure6_isCover

end CoveringDesigns
