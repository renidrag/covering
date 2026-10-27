import CoveringDesigns.PairConsequences.Arithmetic
import CoveringDesigns.Qk_K_2.NumericalLower
import CoveringDesigns.LiftingComparison.Covering

/-! The 78 reviewed direct bounds. Every lift uses the existing universal
residual theorem and retains each ceiling. Comparison categories are dated
metadata, not proof premises or historical novelty claims. -/
namespace CoveringDesigns.PairConsequences

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_42_7_2 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 42) (hB : Multicover.IsCover B 7 2 1) :
    43 ≤ Fintype.card I := by
  classical
  exact indexed_six (by decide) hv hB (by decide)

theorem lower_bound_42_7_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 42) (hC : IsCover C 7 2) : 43 ≤ C.card := by
  classical
  simpa using indexed_lower_42_7_2 hv ((Multicover.ofFamily_isCover_one C 7 2).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_78_13_2 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 78) (hB : Multicover.IsCover B 13 2 1) :
    43 ≤ Fintype.card I := by
  classical
  exact indexed_six (by decide) hv hB (by decide)

theorem lower_bound_78_13_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 78) (hC : IsCover C 13 2) : 43 ≤ C.card := by
  classical
  simpa using indexed_lower_78_13_2 hv ((Multicover.ofFamily_isCover_one C 13 2).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_84_14_2 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 84) (hB : Multicover.IsCover B 14 2 1) :
    43 ≤ Fintype.card I := by
  classical
  exact indexed_six (by decide) hv hB (by decide)

theorem lower_bound_84_14_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 84) (hC : IsCover C 14 2) : 43 ≤ C.card := by
  classical
  simpa using indexed_lower_84_14_2 hv ((Multicover.ofFamily_isCover_one C 14 2).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_90_15_2 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 90) (hB : Multicover.IsCover B 15 2 1) :
    43 ≤ Fintype.card I := by
  classical
  exact indexed_six (by decide) hv hB (by decide)

theorem lower_bound_90_15_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 90) (hC : IsCover C 15 2) : 43 ≤ C.card := by
  classical
  simpa using indexed_lower_90_15_2 hv ((Multicover.ofFamily_isCover_one C 15 2).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_96_16_2 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 96) (hB : Multicover.IsCover B 16 2 1) :
    43 ≤ Fintype.card I := by
  classical
  exact indexed_six (by decide) hv hB (by decide)

theorem lower_bound_96_16_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 96) (hC : IsCover C 16 2) : 43 ≤ C.card := by
  classical
  simpa using indexed_lower_96_16_2 hv ((Multicover.ofFamily_isCover_one C 16 2).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_43_8_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 43) (hB : Multicover.IsCover B 8 3 1) :
    232 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (43-1) (8-1) (3-1) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 43 8 1 43 = 232 := by decide
  exact he ▸ h

theorem lower_bound_43_8_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 43) (hC : IsCover C 8 3) : 232 ≤ C.card := by
  classical
  simpa using indexed_lower_43_8_3 hv ((Multicover.ofFamily_isCover_one C 8 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_56_12_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 56) (hB : Multicover.IsCover B 12 3 1) :
    145 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (56-1) (12-1) (3-1) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_55_11_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 56 12 1 31 = 145 := by decide
  exact he ▸ h

theorem lower_bound_56_12_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 56) (hC : IsCover C 12 3) : 145 ≤ C.card := by
  classical
  simpa using indexed_lower_56_12_3 hv ((Multicover.ofFamily_isCover_one C 12 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_57_9_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 57) (hB : Multicover.IsCover B 9 3 1) :
    361 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (57-1) (9-1) (3-1) 1 57 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_56_8_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 57 9 1 57 = 361 := by decide
  exact he ▸ h

theorem lower_bound_57_9_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 57) (hC : IsCover C 9 3) : 361 ≤ C.card := by
  classical
  simpa using indexed_lower_57_9_3 hv ((Multicover.ofFamily_isCover_one C 9 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_66_14_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 66) (hB : Multicover.IsCover B 14 3 1) :
    147 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (66-1) (14-1) (3-1) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_65_13_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 66 14 1 31 = 147 := by decide
  exact he ▸ h

theorem lower_bound_66_14_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 66) (hC : IsCover C 14 3) : 147 ≤ C.card := by
  classical
  simpa using indexed_lower_66_14_3 hv ((Multicover.ofFamily_isCover_one C 14 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_71_15_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 71) (hB : Multicover.IsCover B 15 3 1) :
    147 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (71-1) (15-1) (3-1) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_70_14_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 71 15 1 31 = 147 := by decide
  exact he ▸ h

theorem lower_bound_71_15_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 71) (hC : IsCover C 15 3) : 147 ≤ C.card := by
  classical
  simpa using indexed_lower_71_15_3 hv ((Multicover.ofFamily_isCover_one C 15 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_79_14_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 79) (hB : Multicover.IsCover B 14 3 1) :
    243 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (79-1) (14-1) (3-1) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 79 14 1 43 = 243 := by decide
  exact he ▸ h

theorem lower_bound_79_14_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 79) (hC : IsCover C 14 3) : 243 ≤ C.card := by
  classical
  simpa using indexed_lower_79_14_3 hv ((Multicover.ofFamily_isCover_one C 14 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_81_17_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 81) (hB : Multicover.IsCover B 17 3 1) :
    148 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (81-1) (17-1) (3-1) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_80_16_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 81 17 1 31 = 148 := by decide
  exact he ▸ h

theorem lower_bound_81_17_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 81) (hC : IsCover C 17 3) : 148 ≤ C.card := by
  classical
  simpa using indexed_lower_81_17_3 hv ((Multicover.ofFamily_isCover_one C 17 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_85_15_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 85) (hB : Multicover.IsCover B 15 3 1) :
    244 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (85-1) (15-1) (3-1) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 85 15 1 43 = 244 := by decide
  exact he ▸ h

theorem lower_bound_85_15_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 85) (hC : IsCover C 15 3) : 244 ≤ C.card := by
  classical
  simpa using indexed_lower_85_15_3 hv ((Multicover.ofFamily_isCover_one C 15 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_86_18_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 86) (hB : Multicover.IsCover B 18 3 1) :
    149 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (86-1) (18-1) (3-1) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_85_17_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 86 18 1 31 = 149 := by decide
  exact he ▸ h

theorem lower_bound_86_18_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 86) (hC : IsCover C 18 3) : 149 ≤ C.card := by
  classical
  simpa using indexed_lower_86_18_3 hv ((Multicover.ofFamily_isCover_one C 18 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_91_11_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 91) (hB : Multicover.IsCover B 11 3 1) :
    753 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (91-1) (11-1) (3-1) 1 91 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_90_10_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 91 11 1 91 = 753 := by decide
  exact he ▸ h

theorem lower_bound_91_11_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 91) (hC : IsCover C 11 3) : 753 ≤ C.card := by
  classical
  simpa using indexed_lower_91_11_3 hv ((Multicover.ofFamily_isCover_one C 11 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_91_16_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 91) (hB : Multicover.IsCover B 16 3 1) :
    245 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (91-1) (16-1) (3-1) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 91 16 1 43 = 245 := by decide
  exact he ▸ h

theorem lower_bound_91_16_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 91) (hC : IsCover C 16 3) : 245 ≤ C.card := by
  classical
  simpa using indexed_lower_91_16_3 hv ((Multicover.ofFamily_isCover_one C 16 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_96_20_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 96) (hB : Multicover.IsCover B 20 3 1) :
    149 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (96-1) (20-1) (3-1) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_95_19_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 96 20 1 31 = 149 := by decide
  exact he ▸ h

theorem lower_bound_96_20_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 96) (hC : IsCover C 20 3) : 149 ≤ C.card := by
  classical
  simpa using indexed_lower_96_20_3 hv ((Multicover.ofFamily_isCover_one C 20 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_97_17_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 97) (hB : Multicover.IsCover B 17 3 1) :
    246 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (97-1) (17-1) (3-1) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 97 17 1 43 = 246 := by decide
  exact he ▸ h

theorem lower_bound_97_17_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 97) (hC : IsCover C 17 3) : 246 ≤ C.card := by
  classical
  simpa using indexed_lower_97_17_3 hv ((Multicover.ofFamily_isCover_one C 17 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_44_9_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 44) (hB : Multicover.IsCover B 9 4 1) :
    1135 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (44-2) (9-2) (4-2) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 44 9 2 43 = 1135 := by decide
  exact he ▸ h

theorem lower_bound_44_9_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 44) (hC : IsCover C 9 4) : 1135 ≤ C.card := by
  classical
  simpa using indexed_lower_44_9_4 hv ((Multicover.ofFamily_isCover_one C 9 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_57_13_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 57) (hB : Multicover.IsCover B 13 4 1) :
    636 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (57-2) (13-2) (4-2) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_55_11_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 57 13 2 31 = 636 := by decide
  exact he ▸ h

theorem lower_bound_57_13_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 57) (hC : IsCover C 13 4) : 636 ≤ C.card := by
  classical
  simpa using indexed_lower_57_13_4 hv ((Multicover.ofFamily_isCover_one C 13 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_58_10_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 58) (hB : Multicover.IsCover B 10 4 1) :
    2094 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (58-2) (10-2) (4-2) 1 57 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_56_8_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 58 10 2 57 = 2094 := by decide
  exact he ▸ h

theorem lower_bound_58_10_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 58) (hC : IsCover C 10 4) : 2094 ≤ C.card := by
  classical
  simpa using indexed_lower_58_10_4 hv ((Multicover.ofFamily_isCover_one C 10 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_67_15_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 67) (hB : Multicover.IsCover B 15 4 1) :
    657 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (67-2) (15-2) (4-2) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_65_13_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 67 15 2 31 = 657 := by decide
  exact he ▸ h

theorem lower_bound_67_15_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 67) (hC : IsCover C 15 4) : 657 ≤ C.card := by
  classical
  simpa using indexed_lower_67_15_4 hv ((Multicover.ofFamily_isCover_one C 15 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_72_16_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 72) (hB : Multicover.IsCover B 16 4 1) :
    662 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (72-2) (16-2) (4-2) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_70_14_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 72 16 2 31 = 662 := by decide
  exact he ▸ h

theorem lower_bound_72_16_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 72) (hC : IsCover C 16 4) : 662 ≤ C.card := by
  classical
  simpa using indexed_lower_72_16_4 hv ((Multicover.ofFamily_isCover_one C 16 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_80_15_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 80) (hB : Multicover.IsCover B 15 4 1) :
    1296 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (80-2) (15-2) (4-2) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 80 15 2 43 = 1296 := by decide
  exact he ▸ h

theorem lower_bound_80_15_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 80) (hC : IsCover C 15 4) : 1296 ≤ C.card := by
  classical
  simpa using indexed_lower_80_15_4 hv ((Multicover.ofFamily_isCover_one C 15 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_82_18_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 82) (hB : Multicover.IsCover B 18 4 1) :
    675 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (82-2) (18-2) (4-2) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_80_16_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 82 18 2 31 = 675 := by decide
  exact he ▸ h

theorem lower_bound_82_18_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 82) (hC : IsCover C 18 4) : 675 ≤ C.card := by
  classical
  simpa using indexed_lower_82_18_4 hv ((Multicover.ofFamily_isCover_one C 18 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_86_16_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 86) (hB : Multicover.IsCover B 16 4 1) :
    1312 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (86-2) (16-2) (4-2) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 86 16 2 43 = 1312 := by decide
  exact he ▸ h

theorem lower_bound_86_16_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 86) (hC : IsCover C 16 4) : 1312 ≤ C.card := by
  classical
  simpa using indexed_lower_86_16_4 hv ((Multicover.ofFamily_isCover_one C 16 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_87_19_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 87) (hB : Multicover.IsCover B 19 4 1) :
    683 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (87-2) (19-2) (4-2) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_85_17_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 87 19 2 31 = 683 := by decide
  exact he ▸ h

theorem lower_bound_87_19_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 87) (hC : IsCover C 19 4) : 683 ≤ C.card := by
  classical
  simpa using indexed_lower_87_19_4 hv ((Multicover.ofFamily_isCover_one C 19 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_92_12_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 92) (hB : Multicover.IsCover B 12 4 1) :
    5773 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (92-2) (12-2) (4-2) 1 91 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_90_10_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 92 12 2 91 = 5773 := by decide
  exact he ▸ h

theorem lower_bound_92_12_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 92) (hC : IsCover C 12 4) : 5773 ≤ C.card := by
  classical
  simpa using indexed_lower_92_12_4 hv ((Multicover.ofFamily_isCover_one C 12 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_92_17_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 92) (hB : Multicover.IsCover B 17 4 1) :
    1326 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (92-2) (17-2) (4-2) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 92 17 2 43 = 1326 := by decide
  exact he ▸ h

theorem lower_bound_92_17_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 92) (hC : IsCover C 17 4) : 1326 ≤ C.card := by
  classical
  simpa using indexed_lower_92_17_4 hv ((Multicover.ofFamily_isCover_one C 17 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_97_21_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 97) (hB : Multicover.IsCover B 21 4 1) :
    689 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (97-2) (21-2) (4-2) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_95_19_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 97 21 2 31 = 689 := by decide
  exact he ▸ h

theorem lower_bound_97_21_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 97) (hC : IsCover C 21 4) : 689 ≤ C.card := by
  classical
  simpa using indexed_lower_97_21_4 hv ((Multicover.ofFamily_isCover_one C 21 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_98_18_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 98) (hB : Multicover.IsCover B 18 4 1) :
    1340 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (98-2) (18-2) (4-2) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 98 18 2 43 = 1340 := by decide
  exact he ▸ h

theorem lower_bound_98_18_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 98) (hC : IsCover C 18 4) : 1340 ≤ C.card := by
  classical
  simpa using indexed_lower_98_18_4 hv ((Multicover.ofFamily_isCover_one C 18 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_45_10_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 45) (hB : Multicover.IsCover B 10 5 1) :
    5108 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (45-3) (10-3) (5-3) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 45 10 3 43 = 5108 := by decide
  exact he ▸ h

theorem lower_bound_45_10_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 45) (hC : IsCover C 10 5) : 5108 ≤ C.card := by
  classical
  simpa using indexed_lower_45_10_5 hv ((Multicover.ofFamily_isCover_one C 10 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_58_14_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 58) (hB : Multicover.IsCover B 14 5 1) :
    2635 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (58-3) (14-3) (5-3) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_55_11_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 58 14 3 31 = 2635 := by decide
  exact he ▸ h

theorem lower_bound_58_14_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 58) (hC : IsCover C 14 5) : 2635 ≤ C.card := by
  classical
  simpa using indexed_lower_58_14_5 hv ((Multicover.ofFamily_isCover_one C 14 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_59_11_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 59) (hB : Multicover.IsCover B 11 5 1) :
    11232 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (59-3) (11-3) (5-3) 1 57 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_56_8_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 59 11 3 57 = 11232 := by decide
  exact he ▸ h

theorem lower_bound_59_11_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 59) (hC : IsCover C 11 5) : 11232 ≤ C.card := by
  classical
  simpa using indexed_lower_59_11_5 hv ((Multicover.ofFamily_isCover_one C 11 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_68_16_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 68) (hB : Multicover.IsCover B 16 5 1) :
    2793 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (68-3) (16-3) (5-3) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_65_13_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 68 16 3 31 = 2793 := by decide
  exact he ▸ h

theorem lower_bound_68_16_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 68) (hC : IsCover C 16 5) : 2793 ≤ C.card := by
  classical
  simpa using indexed_lower_68_16_5 hv ((Multicover.ofFamily_isCover_one C 16 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_73_17_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 73) (hB : Multicover.IsCover B 17 5 1) :
    2843 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (73-3) (17-3) (5-3) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_70_14_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 73 17 3 31 = 2843 := by decide
  exact he ▸ h

theorem lower_bound_73_17_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 73) (hC : IsCover C 17 5) : 2843 ≤ C.card := by
  classical
  simpa using indexed_lower_73_17_5 hv ((Multicover.ofFamily_isCover_one C 17 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_81_16_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 81) (hB : Multicover.IsCover B 16 5 1) :
    6561 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (81-3) (16-3) (5-3) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 81 16 3 43 = 6561 := by decide
  exact he ▸ h

theorem lower_bound_81_16_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 81) (hC : IsCover C 16 5) : 6561 ≤ C.card := by
  classical
  simpa using indexed_lower_81_16_5 hv ((Multicover.ofFamily_isCover_one C 16 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_83_19_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 83) (hB : Multicover.IsCover B 19 5 1) :
    2949 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (83-3) (19-3) (5-3) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_80_16_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 83 19 3 31 = 2949 := by decide
  exact he ▸ h

theorem lower_bound_83_19_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 83) (hC : IsCover C 19 5) : 2949 ≤ C.card := by
  classical
  simpa using indexed_lower_83_19_5 hv ((Multicover.ofFamily_isCover_one C 19 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_87_17_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 87) (hB : Multicover.IsCover B 17 5 1) :
    6715 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (87-3) (17-3) (5-3) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 87 17 3 43 = 6715 := by decide
  exact he ▸ h

theorem lower_bound_87_17_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 87) (hC : IsCover C 17 5) : 6715 ≤ C.card := by
  classical
  simpa using indexed_lower_87_17_5 hv ((Multicover.ofFamily_isCover_one C 17 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_88_20_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 88) (hB : Multicover.IsCover B 20 5 1) :
    3006 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (88-3) (20-3) (5-3) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_85_17_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 88 20 3 31 = 3006 := by decide
  exact he ▸ h

theorem lower_bound_88_20_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 88) (hC : IsCover C 20 5) : 3006 ≤ C.card := by
  classical
  simpa using indexed_lower_88_20_5 hv ((Multicover.ofFamily_isCover_one C 20 5).mpr hC)

-- retained cvkt; comparison inputs retained 27 October 2026.
theorem indexed_lower_93_13_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 93) (hB : Multicover.IsCover B 13 5 1) :
    41300 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (93-3) (13-3) (5-3) 1 91 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_90_10_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 93 13 3 91 = 41300 := by decide
  exact he ▸ h

theorem lower_bound_93_13_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 93) (hC : IsCover C 13 5) : 41300 ≤ C.card := by
  classical
  simpa using indexed_lower_93_13_5 hv ((Multicover.ofFamily_isCover_one C 13 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_93_18_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 93) (hB : Multicover.IsCover B 18 5 1) :
    6851 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (93-3) (18-3) (5-3) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 93 18 3 43 = 6851 := by decide
  exact he ▸ h

theorem lower_bound_93_18_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 93) (hC : IsCover C 18 5) : 6851 ≤ C.card := by
  classical
  simpa using indexed_lower_93_18_5 hv ((Multicover.ofFamily_isCover_one C 18 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_98_22_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 98) (hB : Multicover.IsCover B 22 5 1) :
    3070 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (98-3) (22-3) (5-3) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_95_19_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 98 22 3 31 = 3070 := by decide
  exact he ▸ h

theorem lower_bound_98_22_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 98) (hC : IsCover C 22 5) : 3070 ≤ C.card := by
  classical
  simpa using indexed_lower_98_22_5 hv ((Multicover.ofFamily_isCover_one C 22 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_99_19_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 99) (hB : Multicover.IsCover B 19 5 1) :
    6983 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (99-3) (19-3) (5-3) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 99 19 3 43 = 6983 := by decide
  exact he ▸ h

theorem lower_bound_99_19_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 99) (hC : IsCover C 19 5) : 6983 ≤ C.card := by
  classical
  simpa using indexed_lower_99_19_5 hv ((Multicover.ofFamily_isCover_one C 19 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_46_11_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 46) (hB : Multicover.IsCover B 11 6 1) :
    21361 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (46-4) (11-4) (6-4) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 46 11 4 43 = 21361 := by decide
  exact he ▸ h

theorem lower_bound_46_11_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 46) (hC : IsCover C 11 6) : 21361 ≤ C.card := by
  classical
  simpa using indexed_lower_46_11_6 hv ((Multicover.ofFamily_isCover_one C 11 6).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_59_15_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 59) (hB : Multicover.IsCover B 15 6 1) :
    10365 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (59-4) (15-4) (6-4) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_55_11_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 59 15 4 31 = 10365 := by decide
  exact he ▸ h

theorem lower_bound_59_15_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 59) (hC : IsCover C 15 6) : 10365 ≤ C.card := by
  classical
  simpa using indexed_lower_59_15_6 hv ((Multicover.ofFamily_isCover_one C 15 6).mpr hC)

-- retained cvkt; comparison inputs retained 27 October 2026.
theorem indexed_lower_60_12_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 60) (hB : Multicover.IsCover B 12 6 1) :
    56160 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (60-4) (12-4) (6-4) 1 57 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_56_8_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 60 12 4 57 = 56160 := by decide
  exact he ▸ h

theorem lower_bound_60_12_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 60) (hC : IsCover C 12 6) : 56160 ≤ C.card := by
  classical
  simpa using indexed_lower_60_12_6 hv ((Multicover.ofFamily_isCover_one C 12 6).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_69_17_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 69) (hB : Multicover.IsCover B 17 6 1) :
    11337 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (69-4) (17-4) (6-4) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_65_13_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 69 17 4 31 = 11337 := by decide
  exact he ▸ h

theorem lower_bound_69_17_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 69) (hC : IsCover C 17 6) : 11337 ≤ C.card := by
  classical
  simpa using indexed_lower_69_17_6 hv ((Multicover.ofFamily_isCover_one C 17 6).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_74_18_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 74) (hB : Multicover.IsCover B 18 6 1) :
    11688 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (74-4) (18-4) (6-4) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_70_14_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 74 18 4 31 = 11688 := by decide
  exact he ▸ h

theorem lower_bound_74_18_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 74) (hC : IsCover C 18 6) : 11688 ≤ C.card := by
  classical
  simpa using indexed_lower_74_18_6 hv ((Multicover.ofFamily_isCover_one C 18 6).mpr hC)

-- retained cvkt; comparison inputs retained 27 October 2026.
theorem indexed_lower_82_17_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 82) (hB : Multicover.IsCover B 17 6 1) :
    31648 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (82-4) (17-4) (6-4) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 82 17 4 43 = 31648 := by decide
  exact he ▸ h

theorem lower_bound_82_17_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 82) (hC : IsCover C 17 6) : 31648 ≤ C.card := by
  classical
  simpa using indexed_lower_82_17_6 hv ((Multicover.ofFamily_isCover_one C 17 6).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_84_20_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 84) (hB : Multicover.IsCover B 20 6 1) :
    12386 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (84-4) (20-4) (6-4) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_80_16_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 84 20 4 31 = 12386 := by decide
  exact he ▸ h

theorem lower_bound_84_20_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 84) (hC : IsCover C 20 6) : 12386 ≤ C.card := by
  classical
  simpa using indexed_lower_84_20_6 hv ((Multicover.ofFamily_isCover_one C 20 6).mpr hC)

-- retained cvkt; comparison inputs retained 27 October 2026.
theorem indexed_lower_88_18_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 88) (hB : Multicover.IsCover B 18 6 1) :
    32829 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (88-4) (18-4) (6-4) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 88 18 4 43 = 32829 := by decide
  exact he ▸ h

theorem lower_bound_88_18_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 88) (hC : IsCover C 18 6) : 32829 ≤ C.card := by
  classical
  simpa using indexed_lower_88_18_6 hv ((Multicover.ofFamily_isCover_one C 18 6).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_89_21_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 89) (hB : Multicover.IsCover B 21 6 1) :
    12740 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (89-4) (21-4) (6-4) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_85_17_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 89 21 4 31 = 12740 := by decide
  exact he ▸ h

theorem lower_bound_89_21_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 89) (hC : IsCover C 21 6) : 12740 ≤ C.card := by
  classical
  simpa using indexed_lower_89_21_6 hv ((Multicover.ofFamily_isCover_one C 21 6).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_94_14_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 94) (hB : Multicover.IsCover B 14 6 1) :
    277300 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (94-4) (14-4) (6-4) 1 91 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_90_10_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 94 14 4 91 = 277300 := by decide
  exact he ▸ h

theorem lower_bound_94_14_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 94) (hC : IsCover C 14 6) : 277300 ≤ C.card := by
  classical
  simpa using indexed_lower_94_14_6 hv ((Multicover.ofFamily_isCover_one C 14 6).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_94_19_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 94) (hB : Multicover.IsCover B 19 6 1) :
    33895 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (94-4) (19-4) (6-4) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 94 19 4 43 = 33895 := by decide
  exact he ▸ h

theorem lower_bound_94_19_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 94) (hC : IsCover C 19 6) : 33895 ≤ C.card := by
  classical
  simpa using indexed_lower_94_19_6 hv ((Multicover.ofFamily_isCover_one C 19 6).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
theorem indexed_lower_99_23_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 99) (hB : Multicover.IsCover B 23 6 1) :
    13215 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (99-4) (23-4) (6-4) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_95_19_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 99 23 4 31 = 13215 := by decide
  exact he ▸ h

theorem lower_bound_99_23_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 99) (hC : IsCover C 23 6) : 13215 ≤ C.card := by
  classical
  simpa using indexed_lower_99_23_6 hv ((Multicover.ofFamily_isCover_one C 23 6).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_47_12_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 47) (hB : Multicover.IsCover B 12 7 1) :
    83664 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (47-5) (12-5) (7-5) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 47 12 5 43 = 83664 := by decide
  exact he ▸ h

theorem lower_bound_47_12_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 47) (hC : IsCover C 12 7) : 83664 ≤ C.card := by
  classical
  simpa using indexed_lower_47_12_7 hv ((Multicover.ofFamily_isCover_one C 12 7).mpr hC)

-- retained cvkt; comparison inputs retained 27 October 2026.
theorem indexed_lower_60_16_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 60) (hB : Multicover.IsCover B 16 7 1) :
    38869 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (60-5) (16-5) (7-5) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_55_11_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 60 16 5 31 = 38869 := by decide
  exact he ▸ h

theorem lower_bound_60_16_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 60) (hC : IsCover C 16 7) : 38869 ≤ C.card := by
  classical
  simpa using indexed_lower_60_16_7 hv ((Multicover.ofFamily_isCover_one C 16 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_61_13_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 61) (hB : Multicover.IsCover B 13 7 1) :
    263520 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (61-5) (13-5) (7-5) 1 57 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_56_8_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 61 13 5 57 = 263520 := by decide
  exact he ▸ h

theorem lower_bound_61_13_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 61) (hC : IsCover C 13 7) : 263520 ≤ C.card := by
  classical
  simpa using indexed_lower_61_13_7 hv ((Multicover.ofFamily_isCover_one C 13 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_70_18_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 70) (hB : Multicover.IsCover B 18 7 1) :
    44089 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (70-5) (18-5) (7-5) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_65_13_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 70 18 5 31 = 44089 := by decide
  exact he ▸ h

theorem lower_bound_70_18_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 70) (hC : IsCover C 18 7) : 44089 ≤ C.card := by
  classical
  simpa using indexed_lower_70_18_7 hv ((Multicover.ofFamily_isCover_one C 18 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_75_19_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 75) (hB : Multicover.IsCover B 19 7 1) :
    46137 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (75-5) (19-5) (7-5) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_70_14_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 75 19 5 31 = 46137 := by decide
  exact he ▸ h

theorem lower_bound_75_19_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 75) (hC : IsCover C 19 7) : 46137 ≤ C.card := by
  classical
  simpa using indexed_lower_75_19_7 hv ((Multicover.ofFamily_isCover_one C 19 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_83_18_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 83) (hB : Multicover.IsCover B 18 7 1) :
    145933 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (83-5) (18-5) (7-5) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 83 18 5 43 = 145933 := by decide
  exact he ▸ h

theorem lower_bound_83_18_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 83) (hC : IsCover C 18 7) : 145933 ≤ C.card := by
  classical
  simpa using indexed_lower_83_18_7 hv ((Multicover.ofFamily_isCover_one C 18 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_85_21_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 85) (hB : Multicover.IsCover B 21 7 1) :
    50134 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (85-5) (21-5) (7-5) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_80_16_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 85 21 5 31 = 50134 := by decide
  exact he ▸ h

theorem lower_bound_85_21_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 85) (hC : IsCover C 21 7) : 50134 ≤ C.card := by
  classical
  simpa using indexed_lower_85_21_7 hv ((Multicover.ofFamily_isCover_one C 21 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_89_19_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 89) (hB : Multicover.IsCover B 19 7 1) :
    153778 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (89-5) (19-5) (7-5) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 89 19 5 43 = 153778 := by decide
  exact he ▸ h

theorem lower_bound_89_19_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 89) (hC : IsCover C 19 7) : 153778 ≤ C.card := by
  classical
  simpa using indexed_lower_89_19_7 hv ((Multicover.ofFamily_isCover_one C 19 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_90_22_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 90) (hB : Multicover.IsCover B 22 7 1) :
    52119 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (90-5) (22-5) (7-5) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_85_17_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 90 22 5 31 = 52119 := by decide
  exact he ▸ h

theorem lower_bound_90_22_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 90) (hC : IsCover C 22 7) : 52119 ≤ C.card := by
  classical
  simpa using indexed_lower_90_22_7 hv ((Multicover.ofFamily_isCover_one C 22 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_95_15_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 95) (hB : Multicover.IsCover B 15 7 1) :
    1756234 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (95-5) (15-5) (7-5) 1 91 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_90_10_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 95 15 5 91 = 1756234 := by decide
  exact he ▸ h

theorem lower_bound_95_15_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 95) (hC : IsCover C 15 7) : 1756234 ≤ C.card := by
  classical
  simpa using indexed_lower_95_15_7 hv ((Multicover.ofFamily_isCover_one C 15 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_95_20_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 95) (hB : Multicover.IsCover B 20 7 1) :
    161002 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (95-5) (20-5) (7-5) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 95 20 5 43 = 161002 := by decide
  exact he ▸ h

theorem lower_bound_95_20_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 95) (hC : IsCover C 20 7) : 161002 ≤ C.card := by
  classical
  simpa using indexed_lower_95_20_7 hv ((Multicover.ofFamily_isCover_one C 20 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_48_13_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 48) (hB : Multicover.IsCover B 13 8 1) :
    308914 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (48-6) (13-6) (8-6) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 48 13 6 43 = 308914 := by decide
  exact he ▸ h

theorem lower_bound_48_13_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 48) (hC : IsCover C 13 8) : 308914 ≤ C.card := by
  classical
  simpa using indexed_lower_48_13_8 hv ((Multicover.ofFamily_isCover_one C 13 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_61_17_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 61) (hB : Multicover.IsCover B 17 8 1) :
    139472 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (61-6) (17-6) (8-6) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_55_11_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 61 17 6 31 = 139472 := by decide
  exact he ▸ h

theorem lower_bound_61_17_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 61) (hC : IsCover C 17 8) : 139472 ≤ C.card := by
  classical
  simpa using indexed_lower_61_17_8 hv ((Multicover.ofFamily_isCover_one C 17 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_62_14_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 62) (hB : Multicover.IsCover B 14 8 1) :
    1167018 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (62-6) (14-6) (8-6) 1 57 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_56_8_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 62 14 6 57 = 1167018 := by decide
  exact he ▸ h

theorem lower_bound_62_14_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 62) (hC : IsCover C 14 8) : 1167018 ≤ C.card := by
  classical
  simpa using indexed_lower_62_14_8 hv ((Multicover.ofFamily_isCover_one C 14 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_71_19_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 71) (hB : Multicover.IsCover B 19 8 1) :
    164754 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (71-6) (19-6) (8-6) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_65_13_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 71 19 6 31 = 164754 := by decide
  exact he ▸ h

theorem lower_bound_71_19_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 71) (hC : IsCover C 19 8) : 164754 ≤ C.card := by
  classical
  simpa using indexed_lower_71_19_8 hv ((Multicover.ofFamily_isCover_one C 19 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_76_20_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 76) (hB : Multicover.IsCover B 20 8 1) :
    175321 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (76-6) (20-6) (8-6) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_70_14_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 76 20 6 31 = 175321 := by decide
  exact he ▸ h

theorem lower_bound_76_20_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 76) (hC : IsCover C 20 8) : 175321 ≤ C.card := by
  classical
  simpa using indexed_lower_76_20_8 hv ((Multicover.ofFamily_isCover_one C 20 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_84_19_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 84) (hB : Multicover.IsCover B 19 8 1) :
    645178 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (84-6) (19-6) (8-6) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 84 19 6 43 = 645178 := by decide
  exact he ▸ h

theorem lower_bound_84_19_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 84) (hC : IsCover C 19 8) : 645178 ≤ C.card := by
  classical
  simpa using indexed_lower_84_19_8 hv ((Multicover.ofFamily_isCover_one C 19 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_86_22_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 86) (hB : Multicover.IsCover B 22 8 1) :
    195979 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (86-6) (22-6) (8-6) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_80_16_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 86 22 6 31 = 195979 := by decide
  exact he ▸ h

theorem lower_bound_86_22_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 86) (hC : IsCover C 22 8) : 195979 ≤ C.card := by
  classical
  simpa using indexed_lower_86_22_8 hv ((Multicover.ofFamily_isCover_one C 22 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_90_20_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 90) (hB : Multicover.IsCover B 20 8 1) :
    692001 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (90-6) (20-6) (8-6) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 90 20 6 43 = 692001 := by decide
  exact he ▸ h

theorem lower_bound_90_20_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 90) (hC : IsCover C 20 8) : 692001 ≤ C.card := by
  classical
  simpa using indexed_lower_90_20_8 hv ((Multicover.ofFamily_isCover_one C 20 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_91_23_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 91) (hB : Multicover.IsCover B 23 8 1) :
    206210 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (91-6) (23-6) (8-6) 1 31 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_85_17_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 91 23 6 31 = 206210 := by decide
  exact he ▸ h

theorem lower_bound_91_23_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 91) (hC : IsCover C 23 8) : 206210 ≤ C.card := by
  classical
  simpa using indexed_lower_91_23_8 hv ((Multicover.ofFamily_isCover_one C 23 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_96_16_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 96) (hB : Multicover.IsCover B 16 8 1) :
    10537404 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (96-6) (16-6) (8-6) 1 91 := by
    intro Y J _ _ _ D hn hD
    classical
    exact Qk_K_2.indexed_lower_90_10_2 hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 96 16 6 91 = 10537404 := by decide
  exact he ▸ h

theorem lower_bound_96_16_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 96) (hC : IsCover C 16 8) : 10537404 ≤ C.card := by
  classical
  simpa using indexed_lower_96_16_8 hv ((Multicover.ofFamily_isCover_one C 16 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
theorem indexed_lower_96_21_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 96) (hB : Multicover.IsCover B 21 8 1) :
    736010 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (96-6) (21-6) (8-6) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_six (by decide) hn hD (by decide)
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 96 21 6 43 = 736010 := by decide
  exact he ▸ h

theorem lower_bound_96_21_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 96) (hC : IsCover C 21 8) : 736010 ≤ C.card := by
  classical
  simpa using indexed_lower_96_21_8 hv ((Multicover.ofFamily_isCover_one C 21 8).mpr hC)

end CoveringDesigns.PairConsequences
