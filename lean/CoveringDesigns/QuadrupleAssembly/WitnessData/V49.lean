import CoveringDesigns.QuadrupleAssembly.WitnessData.V49.Part0

import CoveringDesigns.QuadrupleAssembly.WitnessData.V49.Part1

import CoveringDesigns.QuadrupleAssembly.WitnessData.V49.Part2

import CoveringDesigns.QuadrupleAssembly.WitnessData.V49.Part3

import CoveringDesigns.QuadrupleAssembly.WitnessData.V49.Part4

import CoveringDesigns.QuadrupleAssembly.WitnessData.V49.Part5

set_option Elab.async false

set_option linter.unusedSimpArgs false

set_option maxRecDepth 50000

set_option maxHeartbeats 10000000

namespace CoveringDesigns.QuadrupleAssembly.WitnessData.V49

open SeedData

def fileA : List (Finset (Fin 49)) := [piece0, piece1, piece2, piece3, piece4, piece5, piece6, piece7, piece8, piece9, piece10, piece11, piece12, piece13].flatten

theorem fileA_eq : fileA = transportRows (labelEquiv 4) (aRows 4) := by

  change fileA = transportRows (labelEquiv 4) ((hFromRows (u := 4) Master8.rows).map _)

  rw [labelled_hFrom]

  simp only [fileA, piece0_eq, piece1_eq, piece2_eq, piece3_eq, piece4_eq, piece5_eq, piece6_eq, piece7_eq, piece8_eq, piece9_eq, piece10_eq, piece11_eq, piece12_eq, piece13_eq, Master8.rows, Master8.part0, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileB : List (Finset (Fin 49)) := [piece14, piece15, piece16, piece17, piece18, piece19, piece20, piece21].flatten

theorem fileB_eq : fileB = transportRows (labelEquiv 4) (bRows 4) := by

  change fileB = transportRows (labelEquiv 4) ((gLatinRows (u := 4) GDD2_4.rows).map _)

  rw [labelled_gLatin]

  simp only [fileB, piece14_eq, piece15_eq, piece16_eq, piece17_eq, piece18_eq, piece19_eq, piece20_eq, piece21_eq, GDD2_4.rows, GDD2_4.part0, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileC : List (Finset (Fin 49)) := [piece22, piece23, piece24, piece25].flatten

theorem fileC_eq : fileC = transportRows (labelEquiv 4) (cRows 4) := by

  rw [labelled_cRows]

  have hr : List.finRange 4 = [0,1,2,3] := by decide +kernel

  simp only [fileC, piece22_eq, piece23_eq, piece24_eq, piece25_eq, hr, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileD : List (Finset (Fin 49)) := [piece26, piece27, piece28, piece29, piece30, piece31, piece32, piece33, piece34, piece35, piece36, piece37, piece38, piece39, piece40, piece41, piece42, piece43, piece44, piece45, piece46, piece47, piece48, piece49].flatten

theorem fileD_eq : fileD = transportRows (labelEquiv 4) (dRows 4) := by

  rw [labelled_dIndices]

  have hr : dIndices 4 = [(0,1,0,0),(0,1,0,1),(0,1,1,0),(0,1,1,1),(0,2,0,0),(0,2,0,1),(0,2,1,0),(0,2,1,1),(0,3,0,0),(0,3,0,1),(0,3,1,0),(0,3,1,1),(1,2,0,0),(1,2,0,1),(1,2,1,0),(1,2,1,1),(1,3,0,0),(1,3,0,1),(1,3,1,0),(1,3,1,1),(2,3,0,0),(2,3,0,1),(2,3,1,0),(2,3,1,1)] := by decide +kernel

  simp only [fileD, piece26_eq, piece27_eq, piece28_eq, piece29_eq, piece30_eq, piece31_eq, piece32_eq, piece33_eq, piece34_eq, piece35_eq, piece36_eq, piece37_eq, piece38_eq, piece39_eq, piece40_eq, piece41_eq, piece42_eq, piece43_eq, piece44_eq, piece45_eq, piece46_eq, piece47_eq, piece48_eq, piece49_eq, hr, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def rows : List (Finset (Fin 49)) := fileA ++ fileB ++ fileC ++ fileD

def blocks : Family (Fin 49) := rows.toFinset

theorem rows_eq : rows = labelledRows 4 := by
  rw [rows,fileA_eq,fileB_eq,fileC_eq,fileD_eq,labelledRows_parts]

theorem correspondence : blocks = labelledFamily 4 := congrArg List.toFinset rows_eq

theorem optimal : IsCover blocks 4 3 ∧ blocks.card = 4704 := by
  rw [correspondence]
  exact labelledFamily_optimal (by decide) (by decide)

end CoveringDesigns.QuadrupleAssembly.WitnessData.V49
