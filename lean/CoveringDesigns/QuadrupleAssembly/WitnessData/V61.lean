import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part0

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part1

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part2

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part3

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part4

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part5

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part6

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part7

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part8

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part9

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61.Part10

set_option Elab.async false

set_option linter.unusedSimpArgs false

set_option maxRecDepth 50000

set_option maxHeartbeats 10000000

namespace CoveringDesigns.QuadrupleAssembly.WitnessData.V61

open SeedData

def fileA : List (Finset (Fin 61)) := [piece0, piece1, piece2, piece3, piece4, piece5, piece6, piece7, piece8, piece9, piece10, piece11, piece12, piece13, piece14, piece15, piece16, piece17, piece18, piece19, piece20, piece21, piece22, piece23, piece24, piece25, piece26, piece27, piece28, piece29].flatten

theorem fileA_eq : fileA = transportRows (labelEquiv 5) (aRows 5) := by

  change fileA = transportRows (labelEquiv 5) ((hFromRows (u := 5) Master10.rows).map _)

  rw [labelled_hFrom]

  simp only [fileA, piece0_eq, piece1_eq, piece2_eq, piece3_eq, piece4_eq, piece5_eq, piece6_eq, piece7_eq, piece8_eq, piece9_eq, piece10_eq, piece11_eq, piece12_eq, piece13_eq, piece14_eq, piece15_eq, piece16_eq, piece17_eq, piece18_eq, piece19_eq, piece20_eq, piece21_eq, piece22_eq, piece23_eq, piece24_eq, piece25_eq, piece26_eq, piece27_eq, piece28_eq, piece29_eq, Master10.rows, Master10.part0, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileB : List (Finset (Fin 61)) := [piece30, piece31, piece32, piece33, piece34, piece35, piece36, piece37, piece38, piece39, piece40, piece41, piece42, piece43, piece44].flatten

theorem fileB_eq : fileB = transportRows (labelEquiv 5) (bRows 5) := by

  change fileB = transportRows (labelEquiv 5) ((gFourRows (u := 5) FourGDD3_5.rows).map _)

  rw [labelled_gFour]

  simp only [fileB, piece30_eq, piece31_eq, piece32_eq, piece33_eq, piece34_eq, piece35_eq, piece36_eq, piece37_eq, piece38_eq, piece39_eq, piece40_eq, piece41_eq, piece42_eq, piece43_eq, piece44_eq, FourGDD3_5.rows, FourGDD3_5.part0, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileC : List (Finset (Fin 61)) := [piece45, piece46, piece47, piece48, piece49].flatten

theorem fileC_eq : fileC = transportRows (labelEquiv 5) (cRows 5) := by

  rw [labelled_cRows]

  have hr : List.finRange 5 = [0,1,2,3,4] := by decide +kernel

  simp only [fileC, piece45_eq, piece46_eq, piece47_eq, piece48_eq, piece49_eq, hr, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileD : List (Finset (Fin 61)) := [piece50, piece51, piece52, piece53, piece54, piece55, piece56, piece57, piece58, piece59, piece60, piece61, piece62, piece63, piece64, piece65, piece66, piece67, piece68, piece69, piece70, piece71, piece72, piece73, piece74, piece75, piece76, piece77, piece78, piece79, piece80, piece81, piece82, piece83, piece84, piece85, piece86, piece87, piece88, piece89].flatten

theorem fileD_eq : fileD = transportRows (labelEquiv 5) (dRows 5) := by

  rw [labelled_dIndices]

  have hr : dIndices 5 = [(0,1,0,0),(0,1,0,1),(0,1,1,0),(0,1,1,1),(0,2,0,0),(0,2,0,1),(0,2,1,0),(0,2,1,1),(0,3,0,0),(0,3,0,1),(0,3,1,0),(0,3,1,1),(0,4,0,0),(0,4,0,1),(0,4,1,0),(0,4,1,1),(1,2,0,0),(1,2,0,1),(1,2,1,0),(1,2,1,1),(1,3,0,0),(1,3,0,1),(1,3,1,0),(1,3,1,1),(1,4,0,0),(1,4,0,1),(1,4,1,0),(1,4,1,1),(2,3,0,0),(2,3,0,1),(2,3,1,0),(2,3,1,1),(2,4,0,0),(2,4,0,1),(2,4,1,0),(2,4,1,1),(3,4,0,0),(3,4,0,1),(3,4,1,0),(3,4,1,1)] := by decide +kernel

  simp only [fileD, piece50_eq, piece51_eq, piece52_eq, piece53_eq, piece54_eq, piece55_eq, piece56_eq, piece57_eq, piece58_eq, piece59_eq, piece60_eq, piece61_eq, piece62_eq, piece63_eq, piece64_eq, piece65_eq, piece66_eq, piece67_eq, piece68_eq, piece69_eq, piece70_eq, piece71_eq, piece72_eq, piece73_eq, piece74_eq, piece75_eq, piece76_eq, piece77_eq, piece78_eq, piece79_eq, piece80_eq, piece81_eq, piece82_eq, piece83_eq, piece84_eq, piece85_eq, piece86_eq, piece87_eq, piece88_eq, piece89_eq, hr, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def rows : List (Finset (Fin 61)) := fileA ++ fileB ++ fileC ++ fileD

def blocks : Family (Fin 61) := rows.toFinset

theorem rows_eq : rows = labelledRows 5 := by
  rw [rows,fileA_eq,fileB_eq,fileC_eq,fileD_eq,labelledRows_parts]

theorem correspondence : blocks = labelledFamily 5 := congrArg List.toFinset rows_eq

theorem optimal : IsCover blocks 4 3 ∧ blocks.card = 9150 := by
  rw [correspondence]
  exact labelledFamily_optimal (by decide) (by decide)

end CoveringDesigns.QuadrupleAssembly.WitnessData.V61
