import CoveringDesigns.SaturatedMatching.Exactness
import CoveringDesigns.Foundations.StandardAxioms

/-!
# Affine boundary and saturated matching

Ordinary C(2k−2,k,3)=14 for k≥31, with actual attaining families on arbitrary
finite point types. The indexed threefold pair theorem retains k≥33.
-/
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoMatching.fourteen_le_card
  CoveringDesigns.TwoKMinusTwoMatching.attaining
  CoveringDesigns.TwoKMinusTwoMatching.exactness_on
  CoveringDesigns.TwoKMinusTwoMatching.covering_number
  CoveringDesigns.covering_number_60_31_3
  CoveringDesigns.covering_number_62_32_3
