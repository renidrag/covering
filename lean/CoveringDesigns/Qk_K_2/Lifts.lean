import CoveringDesigns.Qk_K_2.Lifting

/-! All 53 recorded compared descendants, plus kernel checks of every scoped
intermediate ceiling. The six unavailable comparisons have no comparison claim.
Schönheim's recurrence and the unchanged C4k family are the proof premises. -/
namespace CoveringDesigns.Qk_K_2

theorem ceilings_9 :
    Multicover.bound 21 36 9 0 = 21 ∧
    Multicover.bound 21 37 10 1 = 78 ∧
    Multicover.bound 21 38 11 2 = 270 ∧
    Multicover.bound 21 39 12 3 = 878 ∧
    Multicover.bound 21 40 13 4 = 2702 ∧
    Multicover.bound 21 41 14 5 = 7913 ∧
    Multicover.bound 21 42 15 6 = 22157 := by decide

theorem ceilings_10 :
    Multicover.bound 21 40 10 0 = 21 ∧
    Multicover.bound 21 41 11 1 = 79 ∧
    Multicover.bound 21 42 12 2 = 277 ∧
    Multicover.bound 21 43 13 3 = 917 ∧
    Multicover.bound 21 44 14 4 = 2882 ∧
    Multicover.bound 21 45 15 5 = 8646 ∧
    Multicover.bound 21 46 16 6 = 24858 := by decide

theorem ceilings_11 :
    Multicover.bound 21 44 11 0 = 21 ∧
    Multicover.bound 21 45 12 1 = 79 ∧
    Multicover.bound 21 46 13 2 = 280 ∧
    Multicover.bound 21 47 14 3 = 940 ∧
    Multicover.bound 21 48 15 4 = 3008 ∧
    Multicover.bound 21 49 16 5 = 9212 ∧
    Multicover.bound 21 50 17 6 = 27095 := by decide

theorem ceilings_13 :
    Multicover.bound 21 52 13 0 = 21 ∧
    Multicover.bound 21 53 14 1 = 80 ∧
    Multicover.bound 21 54 15 2 = 288 ∧
    Multicover.bound 21 55 16 3 = 990 ∧
    Multicover.bound 21 56 17 4 = 3262 ∧
    Multicover.bound 21 57 18 5 = 10330 ∧
    Multicover.bound 21 58 19 6 = 31534 := by decide

theorem ceilings_14 :
    Multicover.bound 21 56 14 0 = 21 ∧
    Multicover.bound 21 57 15 1 = 80 ∧
    Multicover.bound 21 58 16 2 = 290 ∧
    Multicover.bound 21 59 17 3 = 1007 ∧
    Multicover.bound 21 60 18 4 = 3357 ∧
    Multicover.bound 21 61 19 5 = 10778 ∧
    Multicover.bound 21 62 20 6 = 33412 := by decide

theorem ceilings_15 :
    Multicover.bound 21 60 15 0 = 21 ∧
    Multicover.bound 21 61 16 1 = 81 ∧
    Multicover.bound 21 62 17 2 = 296 ∧
    Multicover.bound 21 63 18 3 = 1036 ∧
    Multicover.bound 21 64 19 4 = 3490 ∧
    Multicover.bound 21 65 20 5 = 11343 ∧
    Multicover.bound 21 66 21 6 = 35650 := by decide

theorem ceilings_17 :
    Multicover.bound 21 68 17 0 = 21 ∧
    Multicover.bound 21 69 18 1 = 81 ∧
    Multicover.bound 21 70 19 2 = 299 ∧
    Multicover.bound 21 71 20 3 = 1062 ∧
    Multicover.bound 21 72 21 4 = 3642 ∧
    Multicover.bound 21 73 22 5 = 12085 ∧
    Multicover.bound 21 74 23 6 = 38883 := by decide

theorem ceilings_18 :
    Multicover.bound 21 72 18 0 = 21 ∧
    Multicover.bound 21 73 19 1 = 81 ∧
    Multicover.bound 21 74 20 2 = 300 ∧
    Multicover.bound 21 75 21 3 = 1072 ∧
    Multicover.bound 21 76 22 4 = 3704 ∧
    Multicover.bound 21 77 23 5 = 12401 ∧
    Multicover.bound 21 78 24 6 = 40304 := by decide

theorem ceilings_19 :
    Multicover.bound 21 76 19 0 = 21 ∧
    Multicover.bound 21 77 20 1 = 81 ∧
    Multicover.bound 21 78 21 2 = 301 ∧
    Multicover.bound 21 79 22 3 = 1081 ∧
    Multicover.bound 21 80 23 4 = 3760 ∧
    Multicover.bound 21 81 24 5 = 12690 := by decide

theorem ceilings_21 :
    Multicover.bound 21 84 21 0 = 21 ∧
    Multicover.bound 21 85 22 1 = 82 ∧
    Multicover.bound 21 86 23 2 = 307 ∧
    Multicover.bound 21 87 24 3 = 1113 := by decide

theorem ceilings_22 :
    Multicover.bound 21 88 22 0 = 21 ∧
    Multicover.bound 21 89 23 1 = 82 ∧
    Multicover.bound 21 90 24 2 = 308 := by decide

theorem ceilings_23 :
    Multicover.bound 21 92 23 0 = 21 ∧
    Multicover.bound 21 93 24 1 = 82 := by decide

/-- C(37,10,3) ≥ 78; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_37_10_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 37) (hC : IsCover C 10 3) : 78 ≤ C.card := by
  have h := lifted_lower_bound 9 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 37 10 1 = 78 := by decide
  exact he ▸ h

/-- C(38,11,4) ≥ 270; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_38_11_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 38) (hC : IsCover C 11 4) : 270 ≤ C.card := by
  have h := lifted_lower_bound 9 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 38 11 2 = 270 := by decide
  exact he ▸ h

/-- C(39,12,5) ≥ 878; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_39_12_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 39) (hC : IsCover C 12 5) : 878 ≤ C.card := by
  have h := lifted_lower_bound 9 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 39 12 3 = 878 := by decide
  exact he ▸ h

/-- C(40,13,6) ≥ 2702; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_40_13_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 40) (hC : IsCover C 13 6) : 2702 ≤ C.card := by
  have h := lifted_lower_bound 9 (by decide) (by decide) 4 hv hC
  have he : Multicover.bound 21 40 13 4 = 2702 := by decide
  exact he ▸ h

/-- C(41,14,7) ≥ 7913; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_41_14_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 41) (hC : IsCover C 14 7) : 7913 ≤ C.card := by
  have h := lifted_lower_bound 9 (by decide) (by decide) 5 hv hC
  have he : Multicover.bound 21 41 14 5 = 7913 := by decide
  exact he ▸ h

/-- C(42,15,8) ≥ 22157; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_42_15_8 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 42) (hC : IsCover C 15 8) : 22157 ≤ C.card := by
  have h := lifted_lower_bound 9 (by decide) (by decide) 6 hv hC
  have he : Multicover.bound 21 42 15 6 = 22157 := by decide
  exact he ▸ h

/-- C(41,11,3) ≥ 79; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_41_11_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 41) (hC : IsCover C 11 3) : 79 ≤ C.card := by
  have h := lifted_lower_bound 10 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 41 11 1 = 79 := by decide
  exact he ▸ h

/-- C(42,12,4) ≥ 277; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_42_12_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 42) (hC : IsCover C 12 4) : 277 ≤ C.card := by
  have h := lifted_lower_bound 10 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 42 12 2 = 277 := by decide
  exact he ▸ h

/-- C(43,13,5) ≥ 917; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_43_13_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 43) (hC : IsCover C 13 5) : 917 ≤ C.card := by
  have h := lifted_lower_bound 10 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 43 13 3 = 917 := by decide
  exact he ▸ h

/-- C(44,14,6) ≥ 2882; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_44_14_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 44) (hC : IsCover C 14 6) : 2882 ≤ C.card := by
  have h := lifted_lower_bound 10 (by decide) (by decide) 4 hv hC
  have he : Multicover.bound 21 44 14 4 = 2882 := by decide
  exact he ▸ h

/-- C(45,15,7) ≥ 8646; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_45_15_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 45) (hC : IsCover C 15 7) : 8646 ≤ C.card := by
  have h := lifted_lower_bound 10 (by decide) (by decide) 5 hv hC
  have he : Multicover.bound 21 45 15 5 = 8646 := by decide
  exact he ▸ h

/-- C(46,16,8) ≥ 24858; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_46_16_8 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 46) (hC : IsCover C 16 8) : 24858 ≤ C.card := by
  have h := lifted_lower_bound 10 (by decide) (by decide) 6 hv hC
  have he : Multicover.bound 21 46 16 6 = 24858 := by decide
  exact he ▸ h

/-- C(45,12,3) ≥ 79; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_45_12_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 45) (hC : IsCover C 12 3) : 79 ≤ C.card := by
  have h := lifted_lower_bound 11 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 45 12 1 = 79 := by decide
  exact he ▸ h

/-- C(46,13,4) ≥ 280; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_46_13_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 46) (hC : IsCover C 13 4) : 280 ≤ C.card := by
  have h := lifted_lower_bound 11 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 46 13 2 = 280 := by decide
  exact he ▸ h

/-- C(47,14,5) ≥ 940; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_47_14_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 47) (hC : IsCover C 14 5) : 940 ≤ C.card := by
  have h := lifted_lower_bound 11 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 47 14 3 = 940 := by decide
  exact he ▸ h

/-- C(48,15,6) ≥ 3008; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_48_15_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 48) (hC : IsCover C 15 6) : 3008 ≤ C.card := by
  have h := lifted_lower_bound 11 (by decide) (by decide) 4 hv hC
  have he : Multicover.bound 21 48 15 4 = 3008 := by decide
  exact he ▸ h

/-- C(49,16,7) ≥ 9212; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_49_16_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 49) (hC : IsCover C 16 7) : 9212 ≤ C.card := by
  have h := lifted_lower_bound 11 (by decide) (by decide) 5 hv hC
  have he : Multicover.bound 21 49 16 5 = 9212 := by decide
  exact he ▸ h

/-- C(53,14,3) ≥ 80; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_53_14_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 53) (hC : IsCover C 14 3) : 80 ≤ C.card := by
  have h := lifted_lower_bound 13 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 53 14 1 = 80 := by decide
  exact he ▸ h

/-- C(54,15,4) ≥ 288; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_54_15_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 54) (hC : IsCover C 15 4) : 288 ≤ C.card := by
  have h := lifted_lower_bound 13 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 54 15 2 = 288 := by decide
  exact he ▸ h

/-- C(55,16,5) ≥ 990; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_55_16_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 55) (hC : IsCover C 16 5) : 990 ≤ C.card := by
  have h := lifted_lower_bound 13 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 55 16 3 = 990 := by decide
  exact he ▸ h

/-- C(56,17,6) ≥ 3262; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_56_17_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 56) (hC : IsCover C 17 6) : 3262 ≤ C.card := by
  have h := lifted_lower_bound 13 (by decide) (by decide) 4 hv hC
  have he : Multicover.bound 21 56 17 4 = 3262 := by decide
  exact he ▸ h

/-- C(57,18,7) ≥ 10330; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_57_18_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 57) (hC : IsCover C 18 7) : 10330 ≤ C.card := by
  have h := lifted_lower_bound 13 (by decide) (by decide) 5 hv hC
  have he : Multicover.bound 21 57 18 5 = 10330 := by decide
  exact he ▸ h

/-- C(57,15,3) ≥ 80; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_57_15_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 57) (hC : IsCover C 15 3) : 80 ≤ C.card := by
  have h := lifted_lower_bound 14 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 57 15 1 = 80 := by decide
  exact he ▸ h

/-- C(58,16,4) ≥ 290; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_58_16_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 58) (hC : IsCover C 16 4) : 290 ≤ C.card := by
  have h := lifted_lower_bound 14 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 58 16 2 = 290 := by decide
  exact he ▸ h

/-- C(59,17,5) ≥ 1007; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_59_17_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 59) (hC : IsCover C 17 5) : 1007 ≤ C.card := by
  have h := lifted_lower_bound 14 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 59 17 3 = 1007 := by decide
  exact he ▸ h

/-- C(60,18,6) ≥ 3357; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_60_18_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 60) (hC : IsCover C 18 6) : 3357 ≤ C.card := by
  have h := lifted_lower_bound 14 (by decide) (by decide) 4 hv hC
  have he : Multicover.bound 21 60 18 4 = 3357 := by decide
  exact he ▸ h

/-- C(61,19,7) ≥ 10778; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_61_19_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 61) (hC : IsCover C 19 7) : 10778 ≤ C.card := by
  have h := lifted_lower_bound 14 (by decide) (by decide) 5 hv hC
  have he : Multicover.bound 21 61 19 5 = 10778 := by decide
  exact he ▸ h

/-- C(61,16,3) ≥ 81; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_61_16_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 61) (hC : IsCover C 16 3) : 81 ≤ C.card := by
  have h := lifted_lower_bound 15 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 61 16 1 = 81 := by decide
  exact he ▸ h

/-- C(62,17,4) ≥ 296; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_62_17_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 62) (hC : IsCover C 17 4) : 296 ≤ C.card := by
  have h := lifted_lower_bound 15 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 62 17 2 = 296 := by decide
  exact he ▸ h

/-- C(63,18,5) ≥ 1036; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_63_18_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 63) (hC : IsCover C 18 5) : 1036 ≤ C.card := by
  have h := lifted_lower_bound 15 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 63 18 3 = 1036 := by decide
  exact he ▸ h

/-- C(64,19,6) ≥ 3490; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_64_19_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 64) (hC : IsCover C 19 6) : 3490 ≤ C.card := by
  have h := lifted_lower_bound 15 (by decide) (by decide) 4 hv hC
  have he : Multicover.bound 21 64 19 4 = 3490 := by decide
  exact he ▸ h

/-- C(65,20,7) ≥ 11343; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_65_20_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 65) (hC : IsCover C 20 7) : 11343 ≤ C.card := by
  have h := lifted_lower_bound 15 (by decide) (by decide) 5 hv hC
  have he : Multicover.bound 21 65 20 5 = 11343 := by decide
  exact he ▸ h

/-- C(69,18,3) ≥ 81; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_69_18_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 69) (hC : IsCover C 18 3) : 81 ≤ C.card := by
  have h := lifted_lower_bound 17 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 69 18 1 = 81 := by decide
  exact he ▸ h

/-- C(70,19,4) ≥ 299; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_70_19_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 70) (hC : IsCover C 19 4) : 299 ≤ C.card := by
  have h := lifted_lower_bound 17 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 70 19 2 = 299 := by decide
  exact he ▸ h

/-- C(71,20,5) ≥ 1062; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_71_20_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 71) (hC : IsCover C 20 5) : 1062 ≤ C.card := by
  have h := lifted_lower_bound 17 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 71 20 3 = 1062 := by decide
  exact he ▸ h

/-- C(72,21,6) ≥ 3642; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_72_21_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 72) (hC : IsCover C 21 6) : 3642 ≤ C.card := by
  have h := lifted_lower_bound 17 (by decide) (by decide) 4 hv hC
  have he : Multicover.bound 21 72 21 4 = 3642 := by decide
  exact he ▸ h

/-- C(73,22,7) ≥ 12085; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_73_22_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 73) (hC : IsCover C 22 7) : 12085 ≤ C.card := by
  have h := lifted_lower_bound 17 (by decide) (by decide) 5 hv hC
  have he : Multicover.bound 21 73 22 5 = 12085 := by decide
  exact he ▸ h

/-- C(73,19,3) ≥ 81; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_73_19_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 73) (hC : IsCover C 19 3) : 81 ≤ C.card := by
  have h := lifted_lower_bound 18 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 73 19 1 = 81 := by decide
  exact he ▸ h

/-- C(74,20,4) ≥ 300; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_74_20_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 74) (hC : IsCover C 20 4) : 300 ≤ C.card := by
  have h := lifted_lower_bound 18 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 74 20 2 = 300 := by decide
  exact he ▸ h

/-- C(75,21,5) ≥ 1072; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_75_21_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 75) (hC : IsCover C 21 5) : 1072 ≤ C.card := by
  have h := lifted_lower_bound 18 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 75 21 3 = 1072 := by decide
  exact he ▸ h

/-- C(76,22,6) ≥ 3704; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_76_22_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 76) (hC : IsCover C 22 6) : 3704 ≤ C.card := by
  have h := lifted_lower_bound 18 (by decide) (by decide) 4 hv hC
  have he : Multicover.bound 21 76 22 4 = 3704 := by decide
  exact he ▸ h

/-- C(77,23,7) ≥ 12401; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_77_23_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 77) (hC : IsCover C 23 7) : 12401 ≤ C.card := by
  have h := lifted_lower_bound 18 (by decide) (by decide) 5 hv hC
  have he : Multicover.bound 21 77 23 5 = 12401 := by decide
  exact he ▸ h

/-- C(77,20,3) ≥ 81; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_77_20_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 77) (hC : IsCover C 20 3) : 81 ≤ C.card := by
  have h := lifted_lower_bound 19 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 77 20 1 = 81 := by decide
  exact he ▸ h

/-- C(78,21,4) ≥ 301; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_78_21_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 78) (hC : IsCover C 21 4) : 301 ≤ C.card := by
  have h := lifted_lower_bound 19 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 78 21 2 = 301 := by decide
  exact he ▸ h

/-- C(79,22,5) ≥ 1081; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_79_22_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 79) (hC : IsCover C 22 5) : 1081 ≤ C.card := by
  have h := lifted_lower_bound 19 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 79 22 3 = 1081 := by decide
  exact he ▸ h

/-- C(80,23,6) ≥ 3760; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_80_23_6 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 80) (hC : IsCover C 23 6) : 3760 ≤ C.card := by
  have h := lifted_lower_bound 19 (by decide) (by decide) 4 hv hC
  have he : Multicover.bound 21 80 23 4 = 3760 := by decide
  exact he ▸ h

/-- C(81,24,7) ≥ 12690; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_81_24_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 81) (hC : IsCover C 24 7) : 12690 ≤ C.card := by
  have h := lifted_lower_bound 19 (by decide) (by decide) 5 hv hC
  have he : Multicover.bound 21 81 24 5 = 12690 := by decide
  exact he ▸ h

/-- C(85,22,3) ≥ 82; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_85_22_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 85) (hC : IsCover C 22 3) : 82 ≤ C.card := by
  have h := lifted_lower_bound 21 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 85 22 1 = 82 := by decide
  exact he ▸ h

/-- C(86,23,4) ≥ 307; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_86_23_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 86) (hC : IsCover C 23 4) : 307 ≤ C.card := by
  have h := lifted_lower_bound 21 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 86 23 2 = 307 := by decide
  exact he ▸ h

/-- C(87,24,5) ≥ 1113; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_87_24_5 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 87) (hC : IsCover C 24 5) : 1113 ≤ C.card := by
  have h := lifted_lower_bound 21 (by decide) (by decide) 3 hv hC
  have he : Multicover.bound 21 87 24 3 = 1113 := by decide
  exact he ▸ h

/-- C(89,23,3) ≥ 82; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_89_23_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 89) (hC : IsCover C 23 3) : 82 ≤ C.card := by
  have h := lifted_lower_bound 22 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 89 23 1 = 82 := by decide
  exact he ▸ h

/-- C(90,24,4) ≥ 308; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_90_24_4 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 90) (hC : IsCover C 24 4) : 308 ≤ C.card := by
  have h := lifted_lower_bound 22 (by decide) (by decide) 2 hv hC
  have he : Multicover.bound 21 90 24 2 = 308 := by decide
  exact he ▸ h

/-- C(93,24,3) ≥ 82; arbitrary finite labels and actual ordinary coverage. -/
theorem lower_bound_93_24_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 93) (hC : IsCover C 24 3) : 82 ≤ C.card := by
  have h := lifted_lower_bound 23 (by decide) (by decide) 1 hv hC
  have he : Multicover.bound 21 93 24 1 = 82 := by decide
  exact he ▸ h

end CoveringDesigns.Qk_K_2
