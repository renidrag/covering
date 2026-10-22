import CoveringDesigns.QuadrupleAssembly.AssemblyRows

/-! Lossless projection of actual distributed blocks; external JSON conversion.
Source: research/c3743-construction-2026-10-22/blocks-37-4-3-1998.json
SHA256: 0ae8ce6798238027f0326e9e7adcf92b5a6f6923b5deca95f2d6a8f4ebe2209c
Provenance, including LJCR-derived filling and seeds: coverings/quadruple-assembly/sources.md. -/

set_option Elab.async false

set_option maxRecDepth 50000

set_option maxHeartbeats 10000000

namespace CoveringDesigns.QuadrupleAssembly.WitnessData.V37

def piece0 : List (Finset (Fin 37)) := [
  {0,6,12,18},
  {0,6,13,19},
  {0,7,12,19},
  {0,7,13,18},
  {1,6,12,19},
  {1,6,13,18},
  {1,7,12,18},
  {1,7,13,19}
]

theorem piece0_eq : piece0 = hPilotPiece {0,3,6,9} := by decide +kernel

def piece1 : List (Finset (Fin 37)) := [
  {0,6,14,20},
  {0,6,15,21},
  {0,7,14,21},
  {0,7,15,20},
  {1,6,14,21},
  {1,6,15,20},
  {1,7,14,20},
  {1,7,15,21}
]

theorem piece1_eq : piece1 = hPilotPiece {0,3,7,10} := by decide +kernel

def piece2 : List (Finset (Fin 37)) := [
  {0,6,16,22},
  {0,6,17,23},
  {0,7,16,23},
  {0,7,17,22},
  {1,6,16,23},
  {1,6,17,22},
  {1,7,16,22},
  {1,7,17,23}
]

theorem piece2_eq : piece2 = hPilotPiece {0,3,8,11} := by decide +kernel

def piece3 : List (Finset (Fin 37)) := [
  {0,6,24,30},
  {0,6,25,31},
  {0,7,24,31},
  {0,7,25,30},
  {1,6,24,31},
  {1,6,25,30},
  {1,7,24,30},
  {1,7,25,31}
]

theorem piece3_eq : piece3 = hPilotPiece {0,3,12,15} := by decide +kernel

def piece4 : List (Finset (Fin 37)) := [
  {0,6,26,32},
  {0,6,27,33},
  {0,7,26,33},
  {0,7,27,32},
  {1,6,26,33},
  {1,6,27,32},
  {1,7,26,32},
  {1,7,27,33}
]

theorem piece4_eq : piece4 = hPilotPiece {0,3,13,16} := by decide +kernel

def piece5 : List (Finset (Fin 37)) := [
  {0,6,28,34},
  {0,6,29,35},
  {0,7,28,35},
  {0,7,29,34},
  {1,6,28,35},
  {1,6,29,34},
  {1,7,28,34},
  {1,7,29,35}
]

theorem piece5_eq : piece5 = hPilotPiece {0,3,14,17} := by decide +kernel

def piece6 : List (Finset (Fin 37)) := [
  {0,8,12,24},
  {0,8,13,25},
  {0,9,12,25},
  {0,9,13,24},
  {1,8,12,25},
  {1,8,13,24},
  {1,9,12,24},
  {1,9,13,25}
]

theorem piece6_eq : piece6 = hPilotPiece {0,4,6,12} := by decide +kernel

def piece7 : List (Finset (Fin 37)) := [
  {0,8,14,28},
  {0,8,15,29},
  {0,9,14,29},
  {0,9,15,28},
  {1,8,14,29},
  {1,8,15,28},
  {1,9,14,28},
  {1,9,15,29}
]

theorem piece7_eq : piece7 = hPilotPiece {0,4,7,14} := by decide +kernel

def piece8 : List (Finset (Fin 37)) := [
  {0,8,16,26},
  {0,8,17,27},
  {0,9,16,27},
  {0,9,17,26},
  {1,8,16,27},
  {1,8,17,26},
  {1,9,16,26},
  {1,9,17,27}
]

theorem piece8_eq : piece8 = hPilotPiece {0,4,8,13} := by decide +kernel

def piece9 : List (Finset (Fin 37)) := [
  {0,8,18,34},
  {0,8,19,35},
  {0,9,18,35},
  {0,9,19,34},
  {1,8,18,35},
  {1,8,19,34},
  {1,9,18,34},
  {1,9,19,35}
]

theorem piece9_eq : piece9 = hPilotPiece {0,4,9,17} := by decide +kernel

def piece10 : List (Finset (Fin 37)) := [
  {0,8,20,32},
  {0,8,21,33},
  {0,9,20,33},
  {0,9,21,32},
  {1,8,20,33},
  {1,8,21,32},
  {1,9,20,32},
  {1,9,21,33}
]

theorem piece10_eq : piece10 = hPilotPiece {0,4,10,16} := by decide +kernel

def piece11 : List (Finset (Fin 37)) := [
  {0,8,22,30},
  {0,8,23,31},
  {0,9,22,31},
  {0,9,23,30},
  {1,8,22,31},
  {1,8,23,30},
  {1,9,22,30},
  {1,9,23,31}
]

theorem piece11_eq : piece11 = hPilotPiece {0,4,11,15} := by decide +kernel

def piece12 : List (Finset (Fin 37)) := [
  {0,10,12,32},
  {0,10,13,33},
  {0,11,12,33},
  {0,11,13,32},
  {1,10,12,33},
  {1,10,13,32},
  {1,11,12,32},
  {1,11,13,33}
]

theorem piece12_eq : piece12 = hPilotPiece {0,5,6,16} := by decide +kernel

def piece13 : List (Finset (Fin 37)) := [
  {0,10,14,30},
  {0,10,15,31},
  {0,11,14,31},
  {0,11,15,30},
  {1,10,14,31},
  {1,10,15,30},
  {1,11,14,30},
  {1,11,15,31}
]

theorem piece13_eq : piece13 = hPilotPiece {0,5,7,15} := by decide +kernel

def piece14 : List (Finset (Fin 37)) := [
  {0,10,16,34},
  {0,10,17,35},
  {0,11,16,35},
  {0,11,17,34},
  {1,10,16,35},
  {1,10,17,34},
  {1,11,16,34},
  {1,11,17,35}
]

theorem piece14_eq : piece14 = hPilotPiece {0,5,8,17} := by decide +kernel

def piece15 : List (Finset (Fin 37)) := [
  {0,10,18,24},
  {0,10,19,25},
  {0,11,18,25},
  {0,11,19,24},
  {1,10,18,25},
  {1,10,19,24},
  {1,11,18,24},
  {1,11,19,25}
]

theorem piece15_eq : piece15 = hPilotPiece {0,5,9,12} := by decide +kernel

def piece16 : List (Finset (Fin 37)) := [
  {0,10,20,28},
  {0,10,21,29},
  {0,11,20,29},
  {0,11,21,28},
  {1,10,20,29},
  {1,10,21,28},
  {1,11,20,28},
  {1,11,21,29}
]

theorem piece16_eq : piece16 = hPilotPiece {0,5,10,14} := by decide +kernel

def piece17 : List (Finset (Fin 37)) := [
  {0,10,22,26},
  {0,10,23,27},
  {0,11,22,27},
  {0,11,23,26},
  {1,10,22,27},
  {1,10,23,26},
  {1,11,22,26},
  {1,11,23,27}
]

theorem piece17_eq : piece17 = hPilotPiece {0,5,11,13} := by decide +kernel

def piece18 : List (Finset (Fin 37)) := [
  {0,12,20,26},
  {0,12,21,27},
  {0,13,20,27},
  {0,13,21,26},
  {1,12,20,27},
  {1,12,21,26},
  {1,13,20,26},
  {1,13,21,27}
]

theorem piece18_eq : piece18 = hPilotPiece {0,6,10,13} := by decide +kernel

def piece19 : List (Finset (Fin 37)) := [
  {0,12,22,34},
  {0,12,23,35},
  {0,13,22,35},
  {0,13,23,34},
  {1,12,22,35},
  {1,12,23,34},
  {1,13,22,34},
  {1,13,23,35}
]

theorem piece19_eq : piece19 = hPilotPiece {0,6,11,17} := by decide +kernel

def piece20 : List (Finset (Fin 37)) := [
  {0,12,28,30},
  {0,12,29,31},
  {0,13,28,31},
  {0,13,29,30},
  {1,12,28,31},
  {1,12,29,30},
  {1,13,28,30},
  {1,13,29,31}
]

theorem piece20_eq : piece20 = hPilotPiece {0,6,14,15} := by decide +kernel

def piece21 : List (Finset (Fin 37)) := [
  {0,14,18,32},
  {0,14,19,33},
  {0,15,18,33},
  {0,15,19,32},
  {1,14,18,33},
  {1,14,19,32},
  {1,15,18,32},
  {1,15,19,33}
]

theorem piece21_eq : piece21 = hPilotPiece {0,7,9,16} := by decide +kernel

def piece22 : List (Finset (Fin 37)) := [
  {0,14,22,24},
  {0,14,23,25},
  {0,15,22,25},
  {0,15,23,24},
  {1,14,22,25},
  {1,14,23,24},
  {1,15,22,24},
  {1,15,23,25}
]

theorem piece22_eq : piece22 = hPilotPiece {0,7,11,12} := by decide +kernel

def piece23 : List (Finset (Fin 37)) := [
  {0,14,26,34},
  {0,14,27,35},
  {0,15,26,35},
  {0,15,27,34},
  {1,14,26,35},
  {1,14,27,34},
  {1,15,26,34},
  {1,15,27,35}
]

theorem piece23_eq : piece23 = hPilotPiece {0,7,13,17} := by decide +kernel

def piece24 : List (Finset (Fin 37)) := [
  {0,16,18,28},
  {0,16,19,29},
  {0,17,18,29},
  {0,17,19,28},
  {1,16,18,29},
  {1,16,19,28},
  {1,17,18,28},
  {1,17,19,29}
]

theorem piece24_eq : piece24 = hPilotPiece {0,8,9,14} := by decide +kernel

def piece25 : List (Finset (Fin 37)) := [
  {0,16,20,30},
  {0,16,21,31},
  {0,17,20,31},
  {0,17,21,30},
  {1,16,20,31},
  {1,16,21,30},
  {1,17,20,30},
  {1,17,21,31}
]

theorem piece25_eq : piece25 = hPilotPiece {0,8,10,15} := by decide +kernel

def piece26 : List (Finset (Fin 37)) := [
  {0,16,24,32},
  {0,16,25,33},
  {0,17,24,33},
  {0,17,25,32},
  {1,16,24,33},
  {1,16,25,32},
  {1,17,24,32},
  {1,17,25,33}
]

theorem piece26_eq : piece26 = hPilotPiece {0,8,12,16} := by decide +kernel

def piece27 : List (Finset (Fin 37)) := [
  {0,18,26,30},
  {0,18,27,31},
  {0,19,26,31},
  {0,19,27,30},
  {1,18,26,31},
  {1,18,27,30},
  {1,19,26,30},
  {1,19,27,31}
]

theorem piece27_eq : piece27 = hPilotPiece {0,9,13,15} := by decide +kernel

def piece28 : List (Finset (Fin 37)) := [
  {0,20,24,34},
  {0,20,25,35},
  {0,21,24,35},
  {0,21,25,34},
  {1,20,24,35},
  {1,20,25,34},
  {1,21,24,34},
  {1,21,25,35}
]

theorem piece28_eq : piece28 = hPilotPiece {0,10,12,17} := by decide +kernel

def piece29 : List (Finset (Fin 37)) := [
  {0,22,28,32},
  {0,22,29,33},
  {0,23,28,33},
  {0,23,29,32},
  {1,22,28,33},
  {1,22,29,32},
  {1,23,28,32},
  {1,23,29,33}
]

theorem piece29_eq : piece29 = hPilotPiece {0,11,14,16} := by decide +kernel

def piece30 : List (Finset (Fin 37)) := [
  {2,6,12,30},
  {2,6,13,31},
  {2,7,12,31},
  {2,7,13,30},
  {3,6,12,31},
  {3,6,13,30},
  {3,7,12,30},
  {3,7,13,31}
]

theorem piece30_eq : piece30 = hPilotPiece {1,3,6,15} := by decide +kernel

def piece31 : List (Finset (Fin 37)) := [
  {2,6,14,34},
  {2,6,15,35},
  {2,7,14,35},
  {2,7,15,34},
  {3,6,14,35},
  {3,6,15,34},
  {3,7,14,34},
  {3,7,15,35}
]

theorem piece31_eq : piece31 = hPilotPiece {1,3,7,17} := by decide +kernel

def piece32 : List (Finset (Fin 37)) := [
  {2,6,16,32},
  {2,6,17,33},
  {2,7,16,33},
  {2,7,17,32},
  {3,6,16,33},
  {3,6,17,32},
  {3,7,16,32},
  {3,7,17,33}
]

theorem piece32_eq : piece32 = hPilotPiece {1,3,8,16} := by decide +kernel

def piece33 : List (Finset (Fin 37)) := [
  {2,6,18,28},
  {2,6,19,29},
  {2,7,18,29},
  {2,7,19,28},
  {3,6,18,29},
  {3,6,19,28},
  {3,7,18,28},
  {3,7,19,29}
]

theorem piece33_eq : piece33 = hPilotPiece {1,3,9,14} := by decide +kernel

def piece34 : List (Finset (Fin 37)) := [
  {2,6,20,26},
  {2,6,21,27},
  {2,7,20,27},
  {2,7,21,26},
  {3,6,20,27},
  {3,6,21,26},
  {3,7,20,26},
  {3,7,21,27}
]

theorem piece34_eq : piece34 = hPilotPiece {1,3,10,13} := by decide +kernel

def piece35 : List (Finset (Fin 37)) := [
  {2,6,22,24},
  {2,6,23,25},
  {2,7,22,25},
  {2,7,23,24},
  {3,6,22,25},
  {3,6,23,24},
  {3,7,22,24},
  {3,7,23,25}
]

theorem piece35_eq : piece35 = hPilotPiece {1,3,11,12} := by decide +kernel

def piece36 : List (Finset (Fin 37)) := [
  {2,8,12,18},
  {2,8,13,19},
  {2,9,12,19},
  {2,9,13,18},
  {3,8,12,19},
  {3,8,13,18},
  {3,9,12,18},
  {3,9,13,19}
]

theorem piece36_eq : piece36 = hPilotPiece {1,4,6,9} := by decide +kernel

def piece37 : List (Finset (Fin 37)) := [
  {2,8,14,20},
  {2,8,15,21},
  {2,9,14,21},
  {2,9,15,20},
  {3,8,14,21},
  {3,8,15,20},
  {3,9,14,20},
  {3,9,15,21}
]

theorem piece37_eq : piece37 = hPilotPiece {1,4,7,10} := by decide +kernel

def piece38 : List (Finset (Fin 37)) := [
  {2,8,16,22},
  {2,8,17,23},
  {2,9,16,23},
  {2,9,17,22},
  {3,8,16,23},
  {3,8,17,22},
  {3,9,16,22},
  {3,9,17,23}
]

theorem piece38_eq : piece38 = hPilotPiece {1,4,8,11} := by decide +kernel

def piece39 : List (Finset (Fin 37)) := [
  {2,8,24,30},
  {2,8,25,31},
  {2,9,24,31},
  {2,9,25,30},
  {3,8,24,31},
  {3,8,25,30},
  {3,9,24,30},
  {3,9,25,31}
]

theorem piece39_eq : piece39 = hPilotPiece {1,4,12,15} := by decide +kernel

def piece40 : List (Finset (Fin 37)) := [
  {2,8,26,32},
  {2,8,27,33},
  {2,9,26,33},
  {2,9,27,32},
  {3,8,26,33},
  {3,8,27,32},
  {3,9,26,32},
  {3,9,27,33}
]

theorem piece40_eq : piece40 = hPilotPiece {1,4,13,16} := by decide +kernel

def piece41 : List (Finset (Fin 37)) := [
  {2,8,28,34},
  {2,8,29,35},
  {2,9,28,35},
  {2,9,29,34},
  {3,8,28,35},
  {3,8,29,34},
  {3,9,28,34},
  {3,9,29,35}
]

theorem piece41_eq : piece41 = hPilotPiece {1,4,14,17} := by decide +kernel

def piece42 : List (Finset (Fin 37)) := [
  {2,10,12,28},
  {2,10,13,29},
  {2,11,12,29},
  {2,11,13,28},
  {3,10,12,29},
  {3,10,13,28},
  {3,11,12,28},
  {3,11,13,29}
]

theorem piece42_eq : piece42 = hPilotPiece {1,5,6,14} := by decide +kernel

def piece43 : List (Finset (Fin 37)) := [
  {2,10,14,26},
  {2,10,15,27},
  {2,11,14,27},
  {2,11,15,26},
  {3,10,14,27},
  {3,10,15,26},
  {3,11,14,26},
  {3,11,15,27}
]

theorem piece43_eq : piece43 = hPilotPiece {1,5,7,13} := by decide +kernel

def piece44 : List (Finset (Fin 37)) := [
  {2,10,16,24},
  {2,10,17,25},
  {2,11,16,25},
  {2,11,17,24},
  {3,10,16,25},
  {3,10,17,24},
  {3,11,16,24},
  {3,11,17,25}
]

theorem piece44_eq : piece44 = hPilotPiece {1,5,8,12} := by decide +kernel

def piece45 : List (Finset (Fin 37)) := [
  {2,10,18,32},
  {2,10,19,33},
  {2,11,18,33},
  {2,11,19,32},
  {3,10,18,33},
  {3,10,19,32},
  {3,11,18,32},
  {3,11,19,33}
]

theorem piece45_eq : piece45 = hPilotPiece {1,5,9,16} := by decide +kernel

def piece46 : List (Finset (Fin 37)) := [
  {2,10,20,30},
  {2,10,21,31},
  {2,11,20,31},
  {2,11,21,30},
  {3,10,20,31},
  {3,10,21,30},
  {3,11,20,30},
  {3,11,21,31}
]

theorem piece46_eq : piece46 = hPilotPiece {1,5,10,15} := by decide +kernel

def piece47 : List (Finset (Fin 37)) := [
  {2,10,22,34},
  {2,10,23,35},
  {2,11,22,35},
  {2,11,23,34},
  {3,10,22,35},
  {3,10,23,34},
  {3,11,22,34},
  {3,11,23,35}
]

theorem piece47_eq : piece47 = hPilotPiece {1,5,11,17} := by decide +kernel

def piece48 : List (Finset (Fin 37)) := [
  {2,12,20,24},
  {2,12,21,25},
  {2,13,20,25},
  {2,13,21,24},
  {3,12,20,25},
  {3,12,21,24},
  {3,13,20,24},
  {3,13,21,25}
]

theorem piece48_eq : piece48 = hPilotPiece {1,6,10,12} := by decide +kernel

def piece49 : List (Finset (Fin 37)) := [
  {2,12,22,32},
  {2,12,23,33},
  {2,13,22,33},
  {2,13,23,32},
  {3,12,22,33},
  {3,12,23,32},
  {3,13,22,32},
  {3,13,23,33}
]

theorem piece49_eq : piece49 = hPilotPiece {1,6,11,16} := by decide +kernel

def piece50 : List (Finset (Fin 37)) := [
  {2,12,26,34},
  {2,12,27,35},
  {2,13,26,35},
  {2,13,27,34},
  {3,12,26,35},
  {3,12,27,34},
  {3,13,26,34},
  {3,13,27,35}
]

theorem piece50_eq : piece50 = hPilotPiece {1,6,13,17} := by decide +kernel

def piece51 : List (Finset (Fin 37)) := [
  {2,14,18,30},
  {2,14,19,31},
  {2,15,18,31},
  {2,15,19,30},
  {3,14,18,31},
  {3,14,19,30},
  {3,15,18,30},
  {3,15,19,31}
]

theorem piece51_eq : piece51 = hPilotPiece {1,7,9,15} := by decide +kernel

def piece52 : List (Finset (Fin 37)) := [
  {2,14,22,28},
  {2,14,23,29},
  {2,15,22,29},
  {2,15,23,28},
  {3,14,22,29},
  {3,14,23,28},
  {3,15,22,28},
  {3,15,23,29}
]

theorem piece52_eq : piece52 = hPilotPiece {1,7,11,14} := by decide +kernel

def piece53 : List (Finset (Fin 37)) := [
  {2,14,24,32},
  {2,14,25,33},
  {2,15,24,33},
  {2,15,25,32},
  {3,14,24,33},
  {3,14,25,32},
  {3,15,24,32},
  {3,15,25,33}
]

theorem piece53_eq : piece53 = hPilotPiece {1,7,12,16} := by decide +kernel

def piece54 : List (Finset (Fin 37)) := [
  {2,16,18,26},
  {2,16,19,27},
  {2,17,18,27},
  {2,17,19,26},
  {3,16,18,27},
  {3,16,19,26},
  {3,17,18,26},
  {3,17,19,27}
]

theorem piece54_eq : piece54 = hPilotPiece {1,8,9,13} := by decide +kernel

def piece55 : List (Finset (Fin 37)) := [
  {2,16,20,34},
  {2,16,21,35},
  {2,17,20,35},
  {2,17,21,34},
  {3,16,20,35},
  {3,16,21,34},
  {3,17,20,34},
  {3,17,21,35}
]

theorem piece55_eq : piece55 = hPilotPiece {1,8,10,17} := by decide +kernel

def piece56 : List (Finset (Fin 37)) := [
  {2,16,28,30},
  {2,16,29,31},
  {2,17,28,31},
  {2,17,29,30},
  {3,16,28,31},
  {3,16,29,30},
  {3,17,28,30},
  {3,17,29,31}
]

theorem piece56_eq : piece56 = hPilotPiece {1,8,14,15} := by decide +kernel

def piece57 : List (Finset (Fin 37)) := [
  {2,18,24,34},
  {2,18,25,35},
  {2,19,24,35},
  {2,19,25,34},
  {3,18,24,35},
  {3,18,25,34},
  {3,19,24,34},
  {3,19,25,35}
]

theorem piece57_eq : piece57 = hPilotPiece {1,9,12,17} := by decide +kernel

def piece58 : List (Finset (Fin 37)) := [
  {2,20,28,32},
  {2,20,29,33},
  {2,21,28,33},
  {2,21,29,32},
  {3,20,28,33},
  {3,20,29,32},
  {3,21,28,32},
  {3,21,29,33}
]

theorem piece58_eq : piece58 = hPilotPiece {1,10,14,16} := by decide +kernel

def piece59 : List (Finset (Fin 37)) := [
  {2,22,26,30},
  {2,22,27,31},
  {2,23,26,31},
  {2,23,27,30},
  {3,22,26,31},
  {3,22,27,30},
  {3,23,26,30},
  {3,23,27,31}
]

theorem piece59_eq : piece59 = hPilotPiece {1,11,13,15} := by decide +kernel

def piece60 : List (Finset (Fin 37)) := [
  {4,6,12,26},
  {4,6,13,27},
  {4,7,12,27},
  {4,7,13,26},
  {5,6,12,27},
  {5,6,13,26},
  {5,7,12,26},
  {5,7,13,27}
]

theorem piece60_eq : piece60 = hPilotPiece {2,3,6,13} := by decide +kernel

def piece61 : List (Finset (Fin 37)) := [
  {4,6,14,24},
  {4,6,15,25},
  {4,7,14,25},
  {4,7,15,24},
  {5,6,14,25},
  {5,6,15,24},
  {5,7,14,24},
  {5,7,15,25}
]

theorem piece61_eq : piece61 = hPilotPiece {2,3,7,12} := by decide +kernel

def piece62 : List (Finset (Fin 37)) := [
  {4,6,16,28},
  {4,6,17,29},
  {4,7,16,29},
  {4,7,17,28},
  {5,6,16,29},
  {5,6,17,28},
  {5,7,16,28},
  {5,7,17,29}
]

theorem piece62_eq : piece62 = hPilotPiece {2,3,8,14} := by decide +kernel

def piece63 : List (Finset (Fin 37)) := [
  {4,6,18,30},
  {4,6,19,31},
  {4,7,18,31},
  {4,7,19,30},
  {5,6,18,31},
  {5,6,19,30},
  {5,7,18,30},
  {5,7,19,31}
]

theorem piece63_eq : piece63 = hPilotPiece {2,3,9,15} := by decide +kernel

def piece64 : List (Finset (Fin 37)) := [
  {4,6,20,34},
  {4,6,21,35},
  {4,7,20,35},
  {4,7,21,34},
  {5,6,20,35},
  {5,6,21,34},
  {5,7,20,34},
  {5,7,21,35}
]

theorem piece64_eq : piece64 = hPilotPiece {2,3,10,17} := by decide +kernel

def piece65 : List (Finset (Fin 37)) := [
  {4,6,22,32},
  {4,6,23,33},
  {4,7,22,33},
  {4,7,23,32},
  {5,6,22,33},
  {5,6,23,32},
  {5,7,22,32},
  {5,7,23,33}
]

theorem piece65_eq : piece65 = hPilotPiece {2,3,11,16} := by decide +kernel

def piece66 : List (Finset (Fin 37)) := [
  {4,8,12,34},
  {4,8,13,35},
  {4,9,12,35},
  {4,9,13,34},
  {5,8,12,35},
  {5,8,13,34},
  {5,9,12,34},
  {5,9,13,35}
]

theorem piece66_eq : piece66 = hPilotPiece {2,4,6,17} := by decide +kernel

def piece67 : List (Finset (Fin 37)) := [
  {4,8,14,32},
  {4,8,15,33},
  {4,9,14,33},
  {4,9,15,32},
  {5,8,14,33},
  {5,8,15,32},
  {5,9,14,32},
  {5,9,15,33}
]

theorem piece67_eq : piece67 = hPilotPiece {2,4,7,16} := by decide +kernel

def piece68 : List (Finset (Fin 37)) := [
  {4,8,16,30},
  {4,8,17,31},
  {4,9,16,31},
  {4,9,17,30},
  {5,8,16,31},
  {5,8,17,30},
  {5,9,16,30},
  {5,9,17,31}
]

theorem piece68_eq : piece68 = hPilotPiece {2,4,8,15} := by decide +kernel

def piece69 : List (Finset (Fin 37)) := [
  {4,8,18,26},
  {4,8,19,27},
  {4,9,18,27},
  {4,9,19,26},
  {5,8,18,27},
  {5,8,19,26},
  {5,9,18,26},
  {5,9,19,27}
]

theorem piece69_eq : piece69 = hPilotPiece {2,4,9,13} := by decide +kernel

def piece70 : List (Finset (Fin 37)) := [
  {4,8,20,24},
  {4,8,21,25},
  {4,9,20,25},
  {4,9,21,24},
  {5,8,20,25},
  {5,8,21,24},
  {5,9,20,24},
  {5,9,21,25}
]

theorem piece70_eq : piece70 = hPilotPiece {2,4,10,12} := by decide +kernel

def piece71 : List (Finset (Fin 37)) := [
  {4,8,22,28},
  {4,8,23,29},
  {4,9,22,29},
  {4,9,23,28},
  {5,8,22,29},
  {5,8,23,28},
  {5,9,22,28},
  {5,9,23,29}
]

theorem piece71_eq : piece71 = hPilotPiece {2,4,11,14} := by decide +kernel

def piece72 : List (Finset (Fin 37)) := [
  {4,10,12,18},
  {4,10,13,19},
  {4,11,12,19},
  {4,11,13,18},
  {5,10,12,19},
  {5,10,13,18},
  {5,11,12,18},
  {5,11,13,19}
]

theorem piece72_eq : piece72 = hPilotPiece {2,5,6,9} := by decide +kernel

def piece73 : List (Finset (Fin 37)) := [
  {4,10,14,20},
  {4,10,15,21},
  {4,11,14,21},
  {4,11,15,20},
  {5,10,14,21},
  {5,10,15,20},
  {5,11,14,20},
  {5,11,15,21}
]

theorem piece73_eq : piece73 = hPilotPiece {2,5,7,10} := by decide +kernel

def piece74 : List (Finset (Fin 37)) := [
  {4,10,16,22},
  {4,10,17,23},
  {4,11,16,23},
  {4,11,17,22},
  {5,10,16,23},
  {5,10,17,22},
  {5,11,16,22},
  {5,11,17,23}
]

theorem piece74_eq : piece74 = hPilotPiece {2,5,8,11} := by decide +kernel

def piece75 : List (Finset (Fin 37)) := [
  {4,10,24,30},
  {4,10,25,31},
  {4,11,24,31},
  {4,11,25,30},
  {5,10,24,31},
  {5,10,25,30},
  {5,11,24,30},
  {5,11,25,31}
]

theorem piece75_eq : piece75 = hPilotPiece {2,5,12,15} := by decide +kernel

def piece76 : List (Finset (Fin 37)) := [
  {4,10,26,32},
  {4,10,27,33},
  {4,11,26,33},
  {4,11,27,32},
  {5,10,26,33},
  {5,10,27,32},
  {5,11,26,32},
  {5,11,27,33}
]

theorem piece76_eq : piece76 = hPilotPiece {2,5,13,16} := by decide +kernel

def piece77 : List (Finset (Fin 37)) := [
  {4,10,28,34},
  {4,10,29,35},
  {4,11,28,35},
  {4,11,29,34},
  {5,10,28,35},
  {5,10,29,34},
  {5,11,28,34},
  {5,11,29,35}
]

theorem piece77_eq : piece77 = hPilotPiece {2,5,14,17} := by decide +kernel

def piece78 : List (Finset (Fin 37)) := [
  {4,12,20,28},
  {4,12,21,29},
  {4,13,20,29},
  {4,13,21,28},
  {5,12,20,29},
  {5,12,21,28},
  {5,13,20,28},
  {5,13,21,29}
]

theorem piece78_eq : piece78 = hPilotPiece {2,6,10,14} := by decide +kernel

def piece79 : List (Finset (Fin 37)) := [
  {4,12,22,30},
  {4,12,23,31},
  {4,13,22,31},
  {4,13,23,30},
  {5,12,22,31},
  {5,12,23,30},
  {5,13,22,30},
  {5,13,23,31}
]

theorem piece79_eq : piece79 = hPilotPiece {2,6,11,15} := by decide +kernel

def piece80 : List (Finset (Fin 37)) := [
  {4,12,24,32},
  {4,12,25,33},
  {4,13,24,33},
  {4,13,25,32},
  {5,12,24,33},
  {5,12,25,32},
  {5,13,24,32},
  {5,13,25,33}
]

theorem piece80_eq : piece80 = hPilotPiece {2,6,12,16} := by decide +kernel

def piece81 : List (Finset (Fin 37)) := [
  {4,14,18,34},
  {4,14,19,35},
  {4,15,18,35},
  {4,15,19,34},
  {5,14,18,35},
  {5,14,19,34},
  {5,15,18,34},
  {5,15,19,35}
]

theorem piece81_eq : piece81 = hPilotPiece {2,7,9,17} := by decide +kernel

def piece82 : List (Finset (Fin 37)) := [
  {4,14,22,26},
  {4,14,23,27},
  {4,15,22,27},
  {4,15,23,26},
  {5,14,22,27},
  {5,14,23,26},
  {5,15,22,26},
  {5,15,23,27}
]

theorem piece82_eq : piece82 = hPilotPiece {2,7,11,13} := by decide +kernel

def piece83 : List (Finset (Fin 37)) := [
  {4,14,28,30},
  {4,14,29,31},
  {4,15,28,31},
  {4,15,29,30},
  {5,14,28,31},
  {5,14,29,30},
  {5,15,28,30},
  {5,15,29,31}
]

theorem piece83_eq : piece83 = hPilotPiece {2,7,14,15} := by decide +kernel

def piece84 : List (Finset (Fin 37)) := [
  {4,16,18,24},
  {4,16,19,25},
  {4,17,18,25},
  {4,17,19,24},
  {5,16,18,25},
  {5,16,19,24},
  {5,17,18,24},
  {5,17,19,25}
]

theorem piece84_eq : piece84 = hPilotPiece {2,8,9,12} := by decide +kernel

def piece85 : List (Finset (Fin 37)) := [
  {4,16,20,32},
  {4,16,21,33},
  {4,17,20,33},
  {4,17,21,32},
  {5,16,20,33},
  {5,16,21,32},
  {5,17,20,32},
  {5,17,21,33}
]

theorem piece85_eq : piece85 = hPilotPiece {2,8,10,16} := by decide +kernel

def piece86 : List (Finset (Fin 37)) := [
  {4,16,26,34},
  {4,16,27,35},
  {4,17,26,35},
  {4,17,27,34},
  {5,16,26,35},
  {5,16,27,34},
  {5,17,26,34},
  {5,17,27,35}
]

theorem piece86_eq : piece86 = hPilotPiece {2,8,13,17} := by decide +kernel

def piece87 : List (Finset (Fin 37)) := [
  {4,18,28,32},
  {4,18,29,33},
  {4,19,28,33},
  {4,19,29,32},
  {5,18,28,33},
  {5,18,29,32},
  {5,19,28,32},
  {5,19,29,33}
]

theorem piece87_eq : piece87 = hPilotPiece {2,9,14,16} := by decide +kernel

def piece88 : List (Finset (Fin 37)) := [
  {4,20,26,30},
  {4,20,27,31},
  {4,21,26,31},
  {4,21,27,30},
  {5,20,26,31},
  {5,20,27,30},
  {5,21,26,30},
  {5,21,27,31}
]

theorem piece88_eq : piece88 = hPilotPiece {2,10,13,15} := by decide +kernel

def piece89 : List (Finset (Fin 37)) := [
  {4,22,24,34},
  {4,22,25,35},
  {4,23,24,35},
  {4,23,25,34},
  {5,22,24,35},
  {5,22,25,34},
  {5,23,24,34},
  {5,23,25,35}
]

theorem piece89_eq : piece89 = hPilotPiece {2,11,12,17} := by decide +kernel

def piece90 : List (Finset (Fin 37)) := [
  {6,12,20,32},
  {6,12,21,33},
  {6,13,20,33},
  {6,13,21,32},
  {7,12,20,33},
  {7,12,21,32},
  {7,13,20,32},
  {7,13,21,33}
]

theorem piece90_eq : piece90 = hPilotPiece {3,6,10,16} := by decide +kernel

def piece91 : List (Finset (Fin 37)) := [
  {6,12,22,28},
  {6,12,23,29},
  {6,13,22,29},
  {6,13,23,28},
  {7,12,22,29},
  {7,12,23,28},
  {7,13,22,28},
  {7,13,23,29}
]

theorem piece91_eq : piece91 = hPilotPiece {3,6,11,14} := by decide +kernel

def piece92 : List (Finset (Fin 37)) := [
  {6,12,24,34},
  {6,12,25,35},
  {6,13,24,35},
  {6,13,25,34},
  {7,12,24,35},
  {7,12,25,34},
  {7,13,24,34},
  {7,13,25,35}
]

theorem piece92_eq : piece92 = hPilotPiece {3,6,12,17} := by decide +kernel

def piece93 : List (Finset (Fin 37)) := [
  {6,14,18,26},
  {6,14,19,27},
  {6,15,18,27},
  {6,15,19,26},
  {7,14,18,27},
  {7,14,19,26},
  {7,15,18,26},
  {7,15,19,27}
]

theorem piece93_eq : piece93 = hPilotPiece {3,7,9,13} := by decide +kernel

def piece94 : List (Finset (Fin 37)) := [
  {6,14,22,30},
  {6,14,23,31},
  {6,15,22,31},
  {6,15,23,30},
  {7,14,22,31},
  {7,14,23,30},
  {7,15,22,30},
  {7,15,23,31}
]

theorem piece94_eq : piece94 = hPilotPiece {3,7,11,15} := by decide +kernel

def piece95 : List (Finset (Fin 37)) := [
  {6,14,28,32},
  {6,14,29,33},
  {6,15,28,33},
  {6,15,29,32},
  {7,14,28,33},
  {7,14,29,32},
  {7,15,28,32},
  {7,15,29,33}
]

theorem piece95_eq : piece95 = hPilotPiece {3,7,14,16} := by decide +kernel

def piece96 : List (Finset (Fin 37)) := [
  {6,16,18,34},
  {6,16,19,35},
  {6,17,18,35},
  {6,17,19,34},
  {7,16,18,35},
  {7,16,19,34},
  {7,17,18,34},
  {7,17,19,35}
]

theorem piece96_eq : piece96 = hPilotPiece {3,8,9,17} := by decide +kernel

def piece97 : List (Finset (Fin 37)) := [
  {6,16,20,24},
  {6,16,21,25},
  {6,17,20,25},
  {6,17,21,24},
  {7,16,20,25},
  {7,16,21,24},
  {7,17,20,24},
  {7,17,21,25}
]

theorem piece97_eq : piece97 = hPilotPiece {3,8,10,12} := by decide +kernel

def piece98 : List (Finset (Fin 37)) := [
  {6,16,26,30},
  {6,16,27,31},
  {6,17,26,31},
  {6,17,27,30},
  {7,16,26,31},
  {7,16,27,30},
  {7,17,26,30},
  {7,17,27,31}
]

theorem piece98_eq : piece98 = hPilotPiece {3,8,13,15} := by decide +kernel

def piece99 : List (Finset (Fin 37)) := [
  {6,18,24,32},
  {6,18,25,33},
  {6,19,24,33},
  {6,19,25,32},
  {7,18,24,33},
  {7,18,25,32},
  {7,19,24,32},
  {7,19,25,33}
]

theorem piece99_eq : piece99 = hPilotPiece {3,9,12,16} := by decide +kernel

def piece100 : List (Finset (Fin 37)) := [
  {6,20,28,30},
  {6,20,29,31},
  {6,21,28,31},
  {6,21,29,30},
  {7,20,28,31},
  {7,20,29,30},
  {7,21,28,30},
  {7,21,29,31}
]

theorem piece100_eq : piece100 = hPilotPiece {3,10,14,15} := by decide +kernel

def piece101 : List (Finset (Fin 37)) := [
  {6,22,26,34},
  {6,22,27,35},
  {6,23,26,35},
  {6,23,27,34},
  {7,22,26,35},
  {7,22,27,34},
  {7,23,26,34},
  {7,23,27,35}
]

theorem piece101_eq : piece101 = hPilotPiece {3,11,13,17} := by decide +kernel

def piece102 : List (Finset (Fin 37)) := [
  {8,12,20,30},
  {8,12,21,31},
  {8,13,20,31},
  {8,13,21,30},
  {9,12,20,31},
  {9,12,21,30},
  {9,13,20,30},
  {9,13,21,31}
]

theorem piece102_eq : piece102 = hPilotPiece {4,6,10,15} := by decide +kernel

def piece103 : List (Finset (Fin 37)) := [
  {8,12,22,26},
  {8,12,23,27},
  {8,13,22,27},
  {8,13,23,26},
  {9,12,22,27},
  {9,12,23,26},
  {9,13,22,26},
  {9,13,23,27}
]

theorem piece103_eq : piece103 = hPilotPiece {4,6,11,13} := by decide +kernel

def piece104 : List (Finset (Fin 37)) := [
  {8,12,28,32},
  {8,12,29,33},
  {8,13,28,33},
  {8,13,29,32},
  {9,12,28,33},
  {9,12,29,32},
  {9,13,28,32},
  {9,13,29,33}
]

theorem piece104_eq : piece104 = hPilotPiece {4,6,14,16} := by decide +kernel

def piece105 : List (Finset (Fin 37)) := [
  {8,14,18,24},
  {8,14,19,25},
  {8,15,18,25},
  {8,15,19,24},
  {9,14,18,25},
  {9,14,19,24},
  {9,15,18,24},
  {9,15,19,25}
]

theorem piece105_eq : piece105 = hPilotPiece {4,7,9,12} := by decide +kernel

def piece106 : List (Finset (Fin 37)) := [
  {8,14,22,34},
  {8,14,23,35},
  {8,15,22,35},
  {8,15,23,34},
  {9,14,22,35},
  {9,14,23,34},
  {9,15,22,34},
  {9,15,23,35}
]

theorem piece106_eq : piece106 = hPilotPiece {4,7,11,17} := by decide +kernel

def piece107 : List (Finset (Fin 37)) := [
  {8,14,26,30},
  {8,14,27,31},
  {8,15,26,31},
  {8,15,27,30},
  {9,14,26,31},
  {9,14,27,30},
  {9,15,26,30},
  {9,15,27,31}
]

theorem piece107_eq : piece107 = hPilotPiece {4,7,13,15} := by decide +kernel

def piece108 : List (Finset (Fin 37)) := [
  {8,16,18,32},
  {8,16,19,33},
  {8,17,18,33},
  {8,17,19,32},
  {9,16,18,33},
  {9,16,19,32},
  {9,17,18,32},
  {9,17,19,33}
]

theorem piece108_eq : piece108 = hPilotPiece {4,8,9,16} := by decide +kernel

def piece109 : List (Finset (Fin 37)) := [
  {8,16,20,28},
  {8,16,21,29},
  {8,17,20,29},
  {8,17,21,28},
  {9,16,20,29},
  {9,16,21,28},
  {9,17,20,28},
  {9,17,21,29}
]

theorem piece109_eq : piece109 = hPilotPiece {4,8,10,14} := by decide +kernel

def piece110 : List (Finset (Fin 37)) := [
  {8,16,24,34},
  {8,16,25,35},
  {8,17,24,35},
  {8,17,25,34},
  {9,16,24,35},
  {9,16,25,34},
  {9,17,24,34},
  {9,17,25,35}
]

theorem piece110_eq : piece110 = hPilotPiece {4,8,12,17} := by decide +kernel

def piece111 : List (Finset (Fin 37)) := [
  {8,18,28,30},
  {8,18,29,31},
  {8,19,28,31},
  {8,19,29,30},
  {9,18,28,31},
  {9,18,29,30},
  {9,19,28,30},
  {9,19,29,31}
]

theorem piece111_eq : piece111 = hPilotPiece {4,9,14,15} := by decide +kernel

end CoveringDesigns.QuadrupleAssembly.WitnessData.V37
