import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part0

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part1

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part2

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part3

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part4

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part5

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part6

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part7

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part8

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part9

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part10

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part11

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part12

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part13

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part14

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part15

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part16

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part17

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part18

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part19

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part20

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part21

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part22

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part23

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part24

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part25

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part26

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part27

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part28

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part29

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part30

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part31

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part32

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part33

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part34

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part35

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part36

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part37

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part38

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part39

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part40

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part41

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97.Part42

set_option Elab.async false

set_option linter.unusedSimpArgs false

set_option maxRecDepth 50000

set_option maxHeartbeats 10000000

namespace CoveringDesigns.QuadrupleAssembly.WitnessData.V97

open SeedData

def fileA : List (Finset (Fin 97)) := [piece0, piece1, piece2, piece3, piece4, piece5, piece6, piece7, piece8, piece9, piece10, piece11, piece12, piece13, piece14, piece15, piece16, piece17, piece18, piece19, piece20, piece21, piece22, piece23, piece24, piece25, piece26, piece27, piece28, piece29, piece30, piece31, piece32, piece33, piece34, piece35, piece36, piece37, piece38, piece39, piece40, piece41, piece42, piece43, piece44, piece45, piece46, piece47, piece48, piece49, piece50, piece51, piece52, piece53, piece54, piece55, piece56, piece57, piece58, piece59, piece60, piece61, piece62, piece63, piece64, piece65, piece66, piece67, piece68, piece69, piece70, piece71, piece72, piece73, piece74, piece75, piece76, piece77, piece78, piece79, piece80, piece81, piece82, piece83, piece84, piece85, piece86, piece87, piece88, piece89, piece90, piece91, piece92, piece93, piece94, piece95, piece96, piece97, piece98, piece99, piece100, piece101, piece102, piece103, piece104, piece105, piece106, piece107, piece108, piece109, piece110, piece111, piece112, piece113, piece114, piece115, piece116, piece117, piece118, piece119, piece120, piece121, piece122, piece123, piece124, piece125, piece126, piece127, piece128, piece129, piece130, piece131, piece132, piece133, piece134, piece135, piece136, piece137, piece138, piece139].flatten

theorem fileA_eq : fileA = transportRows (labelEquiv 8) (aRows 8) := by

  change fileA = transportRows (labelEquiv 8) ((hFromRows (u := 8) Master16.rows).map _)

  rw [labelled_hFrom]

  simp only [fileA, piece0_eq, piece1_eq, piece2_eq, piece3_eq, piece4_eq, piece5_eq, piece6_eq, piece7_eq, piece8_eq, piece9_eq, piece10_eq, piece11_eq, piece12_eq, piece13_eq, piece14_eq, piece15_eq, piece16_eq, piece17_eq, piece18_eq, piece19_eq, piece20_eq, piece21_eq, piece22_eq, piece23_eq, piece24_eq, piece25_eq, piece26_eq, piece27_eq, piece28_eq, piece29_eq, piece30_eq, piece31_eq, piece32_eq, piece33_eq, piece34_eq, piece35_eq, piece36_eq, piece37_eq, piece38_eq, piece39_eq, piece40_eq, piece41_eq, piece42_eq, piece43_eq, piece44_eq, piece45_eq, piece46_eq, piece47_eq, piece48_eq, piece49_eq, piece50_eq, piece51_eq, piece52_eq, piece53_eq, piece54_eq, piece55_eq, piece56_eq, piece57_eq, piece58_eq, piece59_eq, piece60_eq, piece61_eq, piece62_eq, piece63_eq, piece64_eq, piece65_eq, piece66_eq, piece67_eq, piece68_eq, piece69_eq, piece70_eq, piece71_eq, piece72_eq, piece73_eq, piece74_eq, piece75_eq, piece76_eq, piece77_eq, piece78_eq, piece79_eq, piece80_eq, piece81_eq, piece82_eq, piece83_eq, piece84_eq, piece85_eq, piece86_eq, piece87_eq, piece88_eq, piece89_eq, piece90_eq, piece91_eq, piece92_eq, piece93_eq, piece94_eq, piece95_eq, piece96_eq, piece97_eq, piece98_eq, piece99_eq, piece100_eq, piece101_eq, piece102_eq, piece103_eq, piece104_eq, piece105_eq, piece106_eq, piece107_eq, piece108_eq, piece109_eq, piece110_eq, piece111_eq, piece112_eq, piece113_eq, piece114_eq, piece115_eq, piece116_eq, piece117_eq, piece118_eq, piece119_eq, piece120_eq, piece121_eq, piece122_eq, piece123_eq, piece124_eq, piece125_eq, piece126_eq, piece127_eq, piece128_eq, piece129_eq, piece130_eq, piece131_eq, piece132_eq, piece133_eq, piece134_eq, piece135_eq, piece136_eq, piece137_eq, piece138_eq, piece139_eq, Master16.rows, Master16.part0, Master16.part1, Master16.part2, Master16.part3, Master16.part4, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileB : List (Finset (Fin 97)) := [piece140, piece141, piece142, piece143, piece144, piece145, piece146, piece147, piece148, piece149, piece150, piece151, piece152, piece153, piece154, piece155, piece156, piece157, piece158, piece159, piece160, piece161, piece162, piece163, piece164, piece165, piece166, piece167, piece168, piece169, piece170, piece171, piece172, piece173, piece174, piece175, piece176, piece177, piece178, piece179, piece180, piece181].flatten

theorem fileB_eq : fileB = transportRows (labelEquiv 8) (bRows 8) := by

  change fileB = transportRows (labelEquiv 8) ((gFourRows (u := 8) FourGDD3_8.rows).map _)

  rw [labelled_gFour]

  simp only [fileB, piece140_eq, piece141_eq, piece142_eq, piece143_eq, piece144_eq, piece145_eq, piece146_eq, piece147_eq, piece148_eq, piece149_eq, piece150_eq, piece151_eq, piece152_eq, piece153_eq, piece154_eq, piece155_eq, piece156_eq, piece157_eq, piece158_eq, piece159_eq, piece160_eq, piece161_eq, piece162_eq, piece163_eq, piece164_eq, piece165_eq, piece166_eq, piece167_eq, piece168_eq, piece169_eq, piece170_eq, piece171_eq, piece172_eq, piece173_eq, piece174_eq, piece175_eq, piece176_eq, piece177_eq, piece178_eq, piece179_eq, piece180_eq, piece181_eq, FourGDD3_8.rows, FourGDD3_8.part0, FourGDD3_8.part1, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileC : List (Finset (Fin 97)) := [piece182, piece183, piece184, piece185, piece186, piece187, piece188, piece189].flatten

theorem fileC_eq : fileC = transportRows (labelEquiv 8) (cRows 8) := by

  rw [labelled_cRows]

  have hr : List.finRange 8 = [0,1,2,3,4,5,6,7] := by decide +kernel

  simp only [fileC, piece182_eq, piece183_eq, piece184_eq, piece185_eq, piece186_eq, piece187_eq, piece188_eq, piece189_eq, hr, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def fileD : List (Finset (Fin 97)) := [piece190, piece191, piece192, piece193, piece194, piece195, piece196, piece197, piece198, piece199, piece200, piece201, piece202, piece203, piece204, piece205, piece206, piece207, piece208, piece209, piece210, piece211, piece212, piece213, piece214, piece215, piece216, piece217, piece218, piece219, piece220, piece221, piece222, piece223, piece224, piece225, piece226, piece227, piece228, piece229, piece230, piece231, piece232, piece233, piece234, piece235, piece236, piece237, piece238, piece239, piece240, piece241, piece242, piece243, piece244, piece245, piece246, piece247, piece248, piece249, piece250, piece251, piece252, piece253, piece254, piece255, piece256, piece257, piece258, piece259, piece260, piece261, piece262, piece263, piece264, piece265, piece266, piece267, piece268, piece269, piece270, piece271, piece272, piece273, piece274, piece275, piece276, piece277, piece278, piece279, piece280, piece281, piece282, piece283, piece284, piece285, piece286, piece287, piece288, piece289, piece290, piece291, piece292, piece293, piece294, piece295, piece296, piece297, piece298, piece299, piece300, piece301].flatten

theorem fileD_eq : fileD = transportRows (labelEquiv 8) (dRows 8) := by

  rw [labelled_dIndices]

  have hr : dIndices 8 = [(0,1,0,0),(0,1,0,1),(0,1,1,0),(0,1,1,1),(0,2,0,0),(0,2,0,1),(0,2,1,0),(0,2,1,1),(0,3,0,0),(0,3,0,1),(0,3,1,0),(0,3,1,1),(0,4,0,0),(0,4,0,1),(0,4,1,0),(0,4,1,1),(0,5,0,0),(0,5,0,1),(0,5,1,0),(0,5,1,1),(0,6,0,0),(0,6,0,1),(0,6,1,0),(0,6,1,1),(0,7,0,0),(0,7,0,1),(0,7,1,0),(0,7,1,1),(1,2,0,0),(1,2,0,1),(1,2,1,0),(1,2,1,1),(1,3,0,0),(1,3,0,1),(1,3,1,0),(1,3,1,1),(1,4,0,0),(1,4,0,1),(1,4,1,0),(1,4,1,1),(1,5,0,0),(1,5,0,1),(1,5,1,0),(1,5,1,1),(1,6,0,0),(1,6,0,1),(1,6,1,0),(1,6,1,1),(1,7,0,0),(1,7,0,1),(1,7,1,0),(1,7,1,1),(2,3,0,0),(2,3,0,1),(2,3,1,0),(2,3,1,1),(2,4,0,0),(2,4,0,1),(2,4,1,0),(2,4,1,1),(2,5,0,0),(2,5,0,1),(2,5,1,0),(2,5,1,1),(2,6,0,0),(2,6,0,1),(2,6,1,0),(2,6,1,1),(2,7,0,0),(2,7,0,1),(2,7,1,0),(2,7,1,1),(3,4,0,0),(3,4,0,1),(3,4,1,0),(3,4,1,1),(3,5,0,0),(3,5,0,1),(3,5,1,0),(3,5,1,1),(3,6,0,0),(3,6,0,1),(3,6,1,0),(3,6,1,1),(3,7,0,0),(3,7,0,1),(3,7,1,0),(3,7,1,1),(4,5,0,0),(4,5,0,1),(4,5,1,0),(4,5,1,1),(4,6,0,0),(4,6,0,1),(4,6,1,0),(4,6,1,1),(4,7,0,0),(4,7,0,1),(4,7,1,0),(4,7,1,1),(5,6,0,0),(5,6,0,1),(5,6,1,0),(5,6,1,1),(5,7,0,0),(5,7,0,1),(5,7,1,0),(5,7,1,1),(6,7,0,0),(6,7,0,1),(6,7,1,0),(6,7,1,1)] := by decide +kernel

  simp only [fileD, piece190_eq, piece191_eq, piece192_eq, piece193_eq, piece194_eq, piece195_eq, piece196_eq, piece197_eq, piece198_eq, piece199_eq, piece200_eq, piece201_eq, piece202_eq, piece203_eq, piece204_eq, piece205_eq, piece206_eq, piece207_eq, piece208_eq, piece209_eq, piece210_eq, piece211_eq, piece212_eq, piece213_eq, piece214_eq, piece215_eq, piece216_eq, piece217_eq, piece218_eq, piece219_eq, piece220_eq, piece221_eq, piece222_eq, piece223_eq, piece224_eq, piece225_eq, piece226_eq, piece227_eq, piece228_eq, piece229_eq, piece230_eq, piece231_eq, piece232_eq, piece233_eq, piece234_eq, piece235_eq, piece236_eq, piece237_eq, piece238_eq, piece239_eq, piece240_eq, piece241_eq, piece242_eq, piece243_eq, piece244_eq, piece245_eq, piece246_eq, piece247_eq, piece248_eq, piece249_eq, piece250_eq, piece251_eq, piece252_eq, piece253_eq, piece254_eq, piece255_eq, piece256_eq, piece257_eq, piece258_eq, piece259_eq, piece260_eq, piece261_eq, piece262_eq, piece263_eq, piece264_eq, piece265_eq, piece266_eq, piece267_eq, piece268_eq, piece269_eq, piece270_eq, piece271_eq, piece272_eq, piece273_eq, piece274_eq, piece275_eq, piece276_eq, piece277_eq, piece278_eq, piece279_eq, piece280_eq, piece281_eq, piece282_eq, piece283_eq, piece284_eq, piece285_eq, piece286_eq, piece287_eq, piece288_eq, piece289_eq, piece290_eq, piece291_eq, piece292_eq, piece293_eq, piece294_eq, piece295_eq, piece296_eq, piece297_eq, piece298_eq, piece299_eq, piece300_eq, piece301_eq, hr, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.append_nil, List.singleton_append, List.cons_append, List.append_assoc]

def rows : List (Finset (Fin 97)) := fileA ++ fileB ++ fileC ++ fileD

def blocks : Family (Fin 97) := rows.toFinset

theorem rows_eq : rows = labelledRows 8 := by
  rw [rows,fileA_eq,fileB_eq,fileC_eq,fileD_eq,labelledRows_parts]

theorem correspondence : blocks = labelledFamily 8 := congrArg List.toFinset rows_eq

theorem optimal : IsCover blocks 4 3 ∧ blocks.card = 37248 := by
  rw [correspondence]
  exact labelledFamily_optimal (by decide) (by decide)

end CoveringDesigns.QuadrupleAssembly.WitnessData.V97
