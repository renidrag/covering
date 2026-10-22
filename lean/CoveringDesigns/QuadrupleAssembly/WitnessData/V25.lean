import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward0
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward1
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward2
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward3
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward4
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward5
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward6
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward7
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward8
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward9
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward10
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward11
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward12
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward13
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward14
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward15
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward16
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward17
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward18
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward19
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward20
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward21
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward22
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward23
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Forward24
import Mathlib.Tactic.FinCases
import CoveringDesigns.Schoenheim.LowerBound
namespace CoveringDesigns.QuadrupleAssembly.WitnessData.V25
theorem checked : selectorCoverCheck id 3 rows ownerIndex = true := by
  apply selectorCoverCheck_of_slices id 3 rows ownerIndex (by decide)
  intro a
  fin_cases a
  · exact forward0
  · exact forward1
  · exact forward2
  · exact forward3
  · exact forward4
  · exact forward5
  · exact forward6
  · exact forward7
  · exact forward8
  · exact forward9
  · exact forward10
  · exact forward11
  · exact forward12
  · exact forward13
  · exact forward14
  · exact forward15
  · exact forward16
  · exact forward17
  · exact forward18
  · exact forward19
  · exact forward20
  · exact forward21
  · exact forward22
  · exact forward23
  · exact forward24
theorem valid : IsCover blocks 4 3 := selectorCoverCheck_sound 4 3 rows ownerIndex uniform_checked checked
theorem size : blocks.card = 600 := by
  have hu : blocks.card ≤ 600 := (List.toFinset_card_le rows).trans_eq (by decide +kernel)
  have hl := Schoenheim.lower_bound (by decide : 1 ≤ 3) (by decide : 3 ≤ 4)
    (by decide : 4 ≤ Fintype.card (Fin 25)) valid
  have he : Schoenheim.bound 25 4 3 = 600 := by decide +kernel
  rw [Fintype.card_fin, he] at hl
  exact Nat.le_antisymm hu hl
end CoveringDesigns.QuadrupleAssembly.WitnessData.V25
