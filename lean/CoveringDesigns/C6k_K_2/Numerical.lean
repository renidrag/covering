import CoveringDesigns.C6k_K_2.LowerBound
import CoveringDesigns.LiftingComparison.Covering

/-! The fourteen retained order-six consequences: two seeds and twelve lifts.
Every intermediate ceiling is retained by the existing lifting recurrence. -/
namespace CoveringDesigns.C6k_K_2

-- refreshed LJCR; comparison inputs retained 27 October 2026.
-- (36,6,2) ≥ 43
theorem indexed_lower_36_6_2 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 36) (hB : Multicover.IsCover B 6 2 1) :
    43 ≤ Fintype.card I := by
  classical
  exact indexed_lower_bound (by decide) hv hB

theorem lower_bound_36_6_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 36) (hC : IsCover C 6 2) : 43 ≤ C.card := by
  classical
  simpa using indexed_lower_36_6_2 hv ((Multicover.ofFamily_isCover_one C 6 2).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
-- (72,12,2) ≥ 43
theorem indexed_lower_72_12_2 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 72) (hB : Multicover.IsCover B 12 2 1) :
    43 ≤ Fintype.card I := by
  classical
  exact indexed_lower_bound (by decide) hv hB

theorem lower_bound_72_12_2 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 72) (hC : IsCover C 12 2) : 43 ≤ C.card := by
  classical
  simpa using indexed_lower_72_12_2 hv ((Multicover.ofFamily_isCover_one C 12 2).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
-- (36,6,2) ≥ 43; ⌈1591/7⌉=228
theorem indexed_lower_37_7_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 37) (hB : Multicover.IsCover B 7 3 1) :
    228 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (37-1) (7-1) (3-1) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 37 7 1 43 = 228 := by decide
  exact he ▸ h

theorem lower_bound_37_7_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 37) (hC : IsCover C 7 3) : 228 ≤ C.card := by
  classical
  simpa using indexed_lower_37_7_3 hv ((Multicover.ofFamily_isCover_one C 7 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
-- (72,12,2) ≥ 43; ⌈3139/13⌉=242
theorem indexed_lower_73_13_3 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 73) (hB : Multicover.IsCover B 13 3 1) :
    242 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (73-1) (13-1) (3-1) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 1)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 73 13 1 43 = 242 := by decide
  exact he ▸ h

theorem lower_bound_73_13_3 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 73) (hC : IsCover C 13 3) : 242 ≤ C.card := by
  classical
  simpa using indexed_lower_73_13_3 hv ((Multicover.ofFamily_isCover_one C 13 3).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
-- (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083
theorem indexed_lower_38_8_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 38) (hB : Multicover.IsCover B 8 4 1) :
    1083 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (38-2) (8-2) (4-2) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 38 8 2 43 = 1083 := by decide
  exact he ▸ h

theorem lower_bound_38_8_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 38) (hC : IsCover C 8 4) : 1083 ≤ C.card := by
  classical
  simpa using indexed_lower_38_8_4 hv ((Multicover.ofFamily_isCover_one C 8 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
-- (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280
theorem indexed_lower_74_14_4 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 74) (hB : Multicover.IsCover B 14 4 1) :
    1280 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (74-2) (14-2) (4-2) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 2)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 74 14 2 43 = 1280 := by decide
  exact he ▸ h

theorem lower_bound_74_14_4 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 74) (hC : IsCover C 14 4) : 1280 ≤ C.card := by
  classical
  simpa using indexed_lower_74_14_4 hv ((Multicover.ofFamily_isCover_one C 14 4).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
-- (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083; ⌈42237/9⌉=4693
theorem indexed_lower_39_9_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 39) (hB : Multicover.IsCover B 9 5 1) :
    4693 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (39-3) (9-3) (5-3) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 39 9 3 43 = 4693 := by decide
  exact he ▸ h

theorem lower_bound_39_9_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 39) (hC : IsCover C 9 5) : 4693 ≤ C.card := by
  classical
  simpa using indexed_lower_39_9_5 hv ((Multicover.ofFamily_isCover_one C 9 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
-- (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280; ⌈96000/15⌉=6400
theorem indexed_lower_75_15_5 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 75) (hB : Multicover.IsCover B 15 5 1) :
    6400 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (75-3) (15-3) (5-3) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 3)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 75 15 3 43 = 6400 := by decide
  exact he ▸ h

theorem lower_bound_75_15_5 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 75) (hC : IsCover C 15 5) : 6400 ≤ C.card := by
  classical
  simpa using indexed_lower_75_15_5 hv ((Multicover.ofFamily_isCover_one C 15 5).mpr hC)

-- refreshed LJCR; comparison inputs retained 27 October 2026.
-- (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083; ⌈42237/9⌉=4693; ⌈187720/10⌉=18772
theorem indexed_lower_40_10_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 40) (hB : Multicover.IsCover B 10 6 1) :
    18772 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (40-4) (10-4) (6-4) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 40 10 4 43 = 18772 := by decide
  exact he ▸ h

theorem lower_bound_40_10_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 40) (hC : IsCover C 10 6) : 18772 ≤ C.card := by
  classical
  simpa using indexed_lower_40_10_6 hv ((Multicover.ofFamily_isCover_one C 10 6).mpr hC)

-- retained cvkt; comparison inputs retained 27 October 2026.
-- (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280; ⌈96000/15⌉=6400; ⌈486400/16⌉=30400
theorem indexed_lower_76_16_6 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 76) (hB : Multicover.IsCover B 16 6 1) :
    30400 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (76-4) (16-4) (6-4) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 4)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 76 16 4 43 = 30400 := by decide
  exact he ▸ h

theorem lower_bound_76_16_6 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 76) (hC : IsCover C 16 6) : 30400 ≤ C.card := by
  classical
  simpa using indexed_lower_76_16_6 hv ((Multicover.ofFamily_isCover_one C 16 6).mpr hC)

-- retained cvkt; comparison inputs retained 27 October 2026.
-- (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083; ⌈42237/9⌉=4693; ⌈187720/10⌉=18772; ⌈769652/11⌉=69969
theorem indexed_lower_41_11_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 41) (hB : Multicover.IsCover B 11 7 1) :
    69969 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (41-5) (11-5) (7-5) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 41 11 5 43 = 69969 := by decide
  exact he ▸ h

theorem lower_bound_41_11_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 41) (hC : IsCover C 11 7) : 69969 ≤ C.card := by
  classical
  simpa using indexed_lower_41_11_7 hv ((Multicover.ofFamily_isCover_one C 11 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
-- (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280; ⌈96000/15⌉=6400; ⌈486400/16⌉=30400; ⌈2340800/17⌉=137695
theorem indexed_lower_77_17_7 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 77) (hB : Multicover.IsCover B 17 7 1) :
    137695 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (77-5) (17-5) (7-5) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 5)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 77 17 5 43 = 137695 := by decide
  exact he ▸ h

theorem lower_bound_77_17_7 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 77) (hC : IsCover C 17 7) : 137695 ≤ C.card := by
  classical
  simpa using indexed_lower_77_17_7 hv ((Multicover.ofFamily_isCover_one C 17 7).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
-- (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083; ⌈42237/9⌉=4693; ⌈187720/10⌉=18772; ⌈769652/11⌉=69969; ⌈2938698/12⌉=244892
theorem indexed_lower_42_12_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 42) (hB : Multicover.IsCover B 12 8 1) :
    244892 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (42-6) (12-6) (8-6) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 42 12 6 43 = 244892 := by decide
  exact he ▸ h

theorem lower_bound_42_12_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 42) (hC : IsCover C 12 8) : 244892 ≤ C.card := by
  classical
  simpa using indexed_lower_42_12_8 hv ((Multicover.ofFamily_isCover_one C 12 8).mpr hC)

-- missing; comparison inputs retained 27 October 2026.
-- (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280; ⌈96000/15⌉=6400; ⌈486400/16⌉=30400; ⌈2340800/17⌉=137695; ⌈10740210/18⌉=596679
theorem indexed_lower_78_18_8 {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 78) (hB : Multicover.IsCover B 18 8 1) :
    596679 ≤ Fintype.card I := by
  classical
  have hs : Multicover.CoverLower (78-6) (18-6) (8-6) 1 43 := by
    intro Y J _ _ _ D hn hD
    classical
    exact indexed_lower_bound (by decide) hn hD
  have h := LiftingComparison.indexed_lower_bound (s := 6)
    (by decide) (by decide) (by decide) hs hv hB
  have he : LiftingComparison.iterate 78 18 6 43 = 596679 := by decide
  exact he ▸ h

theorem lower_bound_78_18_8 {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 78) (hC : IsCover C 18 8) : 596679 ≤ C.card := by
  classical
  simpa using indexed_lower_78_18_8 hv ((Multicover.ofFamily_isCover_one C 18 8).mpr hC)

end CoveringDesigns.C6k_K_2
