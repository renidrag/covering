import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part0

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part1

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part2

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part3

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part4

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part5

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part6

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part7

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part8

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part9

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part10

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part11

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part12

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part13

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part14

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part15

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part16

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part17

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part18

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part19

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part20

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part21

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part22

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part23

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part24

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part25

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part26

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part27

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85.Part28

set_option Elab.async false

set_option linter.unusedSimpArgs false

set_option maxRecDepth 50000

set_option maxHeartbeats 10000000

namespace CoveringDesigns.QuadrupleAssembly.WitnessData.V85

open SeedData

def fileA : List (Finset (Fin 85)) := [piece0, piece1, piece2, piece3, piece4, piece5, piece6, piece7, piece8, piece9, piece10, piece11, piece12, piece13, piece14, piece15, piece16, piece17, piece18, piece19, piece20, piece21, piece22, piece23, piece24, piece25, piece26, piece27, piece28, piece29, piece30, piece31, piece32, piece33, piece34, piece35, piece36, piece37, piece38, piece39, piece40, piece41, piece42, piece43, piece44, piece45, piece46, piece47, piece48, piece49, piece50, piece51, piece52, piece53, piece54, piece55, piece56, piece57, piece58, piece59, piece60, piece61, piece62, piece63, piece64, piece65, piece66, piece67, piece68, piece69, piece70, piece71, piece72, piece73, piece74, piece75, piece76, piece77, piece78, piece79, piece80, piece81, piece82, piece83, piece84, piece85, piece86, piece87, piece88, piece89, piece90].flatten

theorem fileA_eq : fileA = transportRows (labelEquiv 7) (aRows 7) := by

  change fileA = transportRows (labelEquiv 7) ((hFromRows (u := 7) Master14.rows).map _)

  rw [labelled_hFrom]

  simp only [fileA, piece0_eq, piece1_eq, piece2_eq, piece3_eq, piece4_eq, piece5_eq, piece6_eq, piece7_eq, piece8_eq, piece9_eq, piece10_eq, piece11_eq, piece12_eq, piece13_eq, piece14_eq, piece15_eq, piece16_eq, piece17_eq, piece18_eq, piece19_eq, piece20_eq, piece21_eq, piece22_eq, piece23_eq, piece24_eq, piece25_eq, piece26_eq, piece27_eq, piece28_eq, piece29_eq, piece30_eq, piece31_eq, piece32_eq, piece33_eq, piece34_eq, piece35_eq, piece36_eq, piece37_eq, piece38_eq, piece39_eq, piece40_eq, piece41_eq, piece42_eq, piece43_eq, piece44_eq, piece45_eq, piece46_eq, piece47_eq, piece48_eq, piece49_eq, piece50_eq, piece51_eq, piece52_eq, piece53_eq, piece54_eq, piece55_eq, piece56_eq, piece57_eq, piece58_eq, piece59_eq, piece60_eq, piece61_eq, piece62_eq, piece63_eq, piece64_eq, piece65_eq, piece66_eq, piece67_eq, piece68_eq, piece69_eq, piece70_eq, piece71_eq, piece72_eq, piece73_eq, piece74_eq, piece75_eq, piece76_eq, piece77_eq, piece78_eq, piece79_eq, piece80_eq, piece81_eq, piece82_eq, piece83_eq, piece84_eq, piece85_eq, piece86_eq, piece87_eq, piece88_eq, piece89_eq, piece90_eq, Master14.rows, Master14.part0, Master14.part1, Master14.part2, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileB : List (Finset (Fin 85)) := [piece91, piece92, piece93, piece94, piece95, piece96, piece97, piece98, piece99, piece100, piece101, piece102, piece103, piece104, piece105, piece106, piece107, piece108, piece109, piece110, piece111, piece112, piece113, piece114, piece115, piece116, piece117, piece118].flatten

theorem fileB_eq : fileB = transportRows (labelEquiv 7) (bRows 7) := by

  change fileB = transportRows (labelEquiv 7) ((gLatinRows (u := 7) GDD2_7.rows).map _)

  rw [labelled_gLatin]

  simp only [fileB, piece91_eq, piece92_eq, piece93_eq, piece94_eq, piece95_eq, piece96_eq, piece97_eq, piece98_eq, piece99_eq, piece100_eq, piece101_eq, piece102_eq, piece103_eq, piece104_eq, piece105_eq, piece106_eq, piece107_eq, piece108_eq, piece109_eq, piece110_eq, piece111_eq, piece112_eq, piece113_eq, piece114_eq, piece115_eq, piece116_eq, piece117_eq, piece118_eq, GDD2_7.rows, GDD2_7.part0, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileC : List (Finset (Fin 85)) := [piece119, piece120, piece121, piece122, piece123, piece124, piece125].flatten

theorem fileC_eq : fileC = transportRows (labelEquiv 7) (cRows 7) := by

  rw [labelled_cRows]

  have hr : List.finRange 7 = [0,1,2,3,4,5,6] := by decide +kernel

  simp only [fileC, piece119_eq, piece120_eq, piece121_eq, piece122_eq, piece123_eq, piece124_eq, piece125_eq, hr, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileD : List (Finset (Fin 85)) := [piece126, piece127, piece128, piece129, piece130, piece131, piece132, piece133, piece134, piece135, piece136, piece137, piece138, piece139, piece140, piece141, piece142, piece143, piece144, piece145, piece146, piece147, piece148, piece149, piece150, piece151, piece152, piece153, piece154, piece155, piece156, piece157, piece158, piece159, piece160, piece161, piece162, piece163, piece164, piece165, piece166, piece167, piece168, piece169, piece170, piece171, piece172, piece173, piece174, piece175, piece176, piece177, piece178, piece179, piece180, piece181, piece182, piece183, piece184, piece185, piece186, piece187, piece188, piece189, piece190, piece191, piece192, piece193, piece194, piece195, piece196, piece197, piece198, piece199, piece200, piece201, piece202, piece203, piece204, piece205, piece206, piece207, piece208, piece209].flatten

theorem fileD_eq : fileD = transportRows (labelEquiv 7) (dRows 7) := by

  rw [labelled_dIndices]

  have hr : dIndices 7 = [(0,1,0,0),(0,1,0,1),(0,1,1,0),(0,1,1,1),(0,2,0,0),(0,2,0,1),(0,2,1,0),(0,2,1,1),(0,3,0,0),(0,3,0,1),(0,3,1,0),(0,3,1,1),(0,4,0,0),(0,4,0,1),(0,4,1,0),(0,4,1,1),(0,5,0,0),(0,5,0,1),(0,5,1,0),(0,5,1,1),(0,6,0,0),(0,6,0,1),(0,6,1,0),(0,6,1,1),(1,2,0,0),(1,2,0,1),(1,2,1,0),(1,2,1,1),(1,3,0,0),(1,3,0,1),(1,3,1,0),(1,3,1,1),(1,4,0,0),(1,4,0,1),(1,4,1,0),(1,4,1,1),(1,5,0,0),(1,5,0,1),(1,5,1,0),(1,5,1,1),(1,6,0,0),(1,6,0,1),(1,6,1,0),(1,6,1,1),(2,3,0,0),(2,3,0,1),(2,3,1,0),(2,3,1,1),(2,4,0,0),(2,4,0,1),(2,4,1,0),(2,4,1,1),(2,5,0,0),(2,5,0,1),(2,5,1,0),(2,5,1,1),(2,6,0,0),(2,6,0,1),(2,6,1,0),(2,6,1,1),(3,4,0,0),(3,4,0,1),(3,4,1,0),(3,4,1,1),(3,5,0,0),(3,5,0,1),(3,5,1,0),(3,5,1,1),(3,6,0,0),(3,6,0,1),(3,6,1,0),(3,6,1,1),(4,5,0,0),(4,5,0,1),(4,5,1,0),(4,5,1,1),(4,6,0,0),(4,6,0,1),(4,6,1,0),(4,6,1,1),(5,6,0,0),(5,6,0,1),(5,6,1,0),(5,6,1,1)] := by decide +kernel

  simp only [fileD, piece126_eq, piece127_eq, piece128_eq, piece129_eq, piece130_eq, piece131_eq, piece132_eq, piece133_eq, piece134_eq, piece135_eq, piece136_eq, piece137_eq, piece138_eq, piece139_eq, piece140_eq, piece141_eq, piece142_eq, piece143_eq, piece144_eq, piece145_eq, piece146_eq, piece147_eq, piece148_eq, piece149_eq, piece150_eq, piece151_eq, piece152_eq, piece153_eq, piece154_eq, piece155_eq, piece156_eq, piece157_eq, piece158_eq, piece159_eq, piece160_eq, piece161_eq, piece162_eq, piece163_eq, piece164_eq, piece165_eq, piece166_eq, piece167_eq, piece168_eq, piece169_eq, piece170_eq, piece171_eq, piece172_eq, piece173_eq, piece174_eq, piece175_eq, piece176_eq, piece177_eq, piece178_eq, piece179_eq, piece180_eq, piece181_eq, piece182_eq, piece183_eq, piece184_eq, piece185_eq, piece186_eq, piece187_eq, piece188_eq, piece189_eq, piece190_eq, piece191_eq, piece192_eq, piece193_eq, piece194_eq, piece195_eq, piece196_eq, piece197_eq, piece198_eq, piece199_eq, piece200_eq, piece201_eq, piece202_eq, piece203_eq, piece204_eq, piece205_eq, piece206_eq, piece207_eq, piece208_eq, piece209_eq, hr, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def rows : List (Finset (Fin 85)) := fileA ++ fileB ++ fileC ++ fileD

def blocks : Family (Fin 85) := rows.toFinset

theorem rows_eq : rows = labelledRows 7 := by
  rw [rows,fileA_eq,fileB_eq,fileC_eq,fileD_eq,labelledRows_parts]

theorem correspondence : blocks = labelledFamily 7 := congrArg List.toFinset rows_eq

theorem optimal : IsCover blocks 4 3 ∧ blocks.card = 24990 := by
  rw [correspondence]
  exact labelledFamily_optimal (by decide) (by decide)

end CoveringDesigns.QuadrupleAssembly.WitnessData.V85
