import CoveringDesigns.C13_7_4.Structural.PairCompatibility
import CoveringDesigns.C13_7_4.Structural.FourPointExclusion
import CoveringDesigns.C13_7_4.Structural.FivePointCount
import CoveringDesigns.C13_7_4.Witness

/-!
A structural proof of C(13,7,4)=30. Stanton and GPPT are proved prerequisites; there are no
classification, search, certificate, or compatibility hypotheses left here.
-/

namespace CoveringDesigns.C13Structural
open Finset

/-- Every four-cover by seven-subsets of a thirteen-point set has at least
thirty blocks. Minimum links force the 15/7/3/1 profile on five points. -/
theorem lower_bound_30 {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} (hn : Fintype.card α = 13) (hC : IsCover C 7 4) :
    30 ≤ C.card := by
  by_cases hb : C.card ≤ 29
  · apply lower_bound_of_pair_quad_obstructions hn hC
    · intro p q hpq hp hq
      exact minimum_pair_degree_seven hn hC hb hp hq hpq
    · intro K hK hmin
      apply bad_quadruple_excluded hn hC hb hK hmin
      intro p hp q hq hpq
      exact minimum_pair_degree_seven hn hC hb (hmin p hp) (hmin q hq) hpq
  · omega

/-- The independently checked thirty-block witness attains the structural
lower bound. The statement has no unproved external prerequisites. -/
theorem covering_number_13_7_4 :
    (∃ C : Family (Fin 13), IsCover C 7 4 ∧ C.card = 30) ∧
    (∀ C : Family (Fin 13), IsCover C 7 4 → 30 ≤ C.card) :=
  ⟨CoveringDesigns.upper_bound_30, fun _ hC => lower_bound_30 (by simp) hC⟩

#guard_standard_axioms lower_bound_30 covering_number_13_7_4
#print axioms covering_number_13_7_4

end CoveringDesigns.C13Structural
