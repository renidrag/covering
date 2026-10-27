import CoveringDesigns.Qk_K_2.Exclusions

namespace CoveringDesigns.Qk_K_2
open PairDivisibility

theorem indexed_lower_55_11_2 {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 55) (hB : Multicover.IsCover B 11 2 1) : 31 ≤ Fintype.card I :=
  improved_floor (q := 5) (by decide) (by decide) hv hB (by decide) (by decide)

theorem lower_bound_55_11_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 55) (hC : IsCover C 11 2) : 31 ≤ C.card := by
  classical
  simpa using indexed_lower_55_11_2 hv ((Multicover.ofFamily_isCover_one C 11 2).mpr hC)

theorem indexed_lower_65_13_2 {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 65) (hB : Multicover.IsCover B 13 2 1) : 31 ≤ Fintype.card I :=
  improved_floor (q := 5) (by decide) (by decide) hv hB (by decide) (by decide)

theorem lower_bound_65_13_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 65) (hC : IsCover C 13 2) : 31 ≤ C.card := by
  classical
  simpa using indexed_lower_65_13_2 hv ((Multicover.ofFamily_isCover_one C 13 2).mpr hC)

theorem indexed_lower_80_16_2 {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 80) (hB : Multicover.IsCover B 16 2 1) : 31 ≤ Fintype.card I :=
  improved_floor (q := 5) (by decide) (by decide) hv hB (by decide) (by decide)

theorem lower_bound_80_16_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 80) (hC : IsCover C 16 2) : 31 ≤ C.card := by
  classical
  simpa using indexed_lower_80_16_2 hv ((Multicover.ofFamily_isCover_one C 16 2).mpr hC)

theorem indexed_lower_85_17_2 {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 85) (hB : Multicover.IsCover B 17 2 1) : 31 ≤ Fintype.card I :=
  improved_floor (q := 5) (by decide) (by decide) hv hB (by decide) (by decide)

theorem lower_bound_85_17_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 85) (hC : IsCover C 17 2) : 31 ≤ C.card := by
  classical
  simpa using indexed_lower_85_17_2 hv ((Multicover.ofFamily_isCover_one C 17 2).mpr hC)

theorem indexed_lower_95_19_2 {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 95) (hB : Multicover.IsCover B 19 2 1) : 31 ≤ Fintype.card I :=
  improved_floor (q := 5) (by decide) (by decide) hv hB (by decide) (by decide)

theorem lower_bound_95_19_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 95) (hC : IsCover C 19 2) : 31 ≤ C.card := by
  classical
  simpa using indexed_lower_95_19_2 hv ((Multicover.ofFamily_isCover_one C 19 2).mpr hC)

theorem indexed_lower_70_14_2 {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 70) (hB : Multicover.IsCover B 14 2 1) : 31 ≤ Fintype.card I :=
  improved_floor (q := 5) (by decide) (by decide) hv hB (by decide) (by decide)

theorem lower_bound_70_14_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 70) (hC : IsCover C 14 2) : 31 ≤ C.card := by
  classical
  simpa using indexed_lower_70_14_2 hv ((Multicover.ofFamily_isCover_one C 14 2).mpr hC)

theorem indexed_lower_56_8_2 {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 56) (hB : Multicover.IsCover B 8 2 1) : 57 ≤ Fintype.card I :=
  indexed_exclusion (q := 7) (by decide) (by decide) hv hB (by decide) no_twisted_seven

theorem lower_bound_56_8_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 56) (hC : IsCover C 8 2) : 57 ≤ C.card := by
  classical
  simpa using indexed_lower_56_8_2 hv ((Multicover.ofFamily_isCover_one C 8 2).mpr hC)

theorem indexed_lower_90_10_2 {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 90) (hB : Multicover.IsCover B 10 2 1) : 91 ≤ Fintype.card I :=
  indexed_exclusion (q := 9) (by decide) (by decide) hv hB (by decide) no_twisted_nine

theorem lower_bound_90_10_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 90) (hC : IsCover C 10 2) : 91 ≤ C.card := by
  classical
  simpa using indexed_lower_90_10_2 hv ((Multicover.ofFamily_isCover_one C 10 2).mpr hC)

end CoveringDesigns.Qk_K_2
