import CoveringDesigns.QuadrupleAssembly.AssemblyRows

/-! Lossless projection of actual distributed blocks; external JSON conversion.
Source: research/c3743-construction-2026-10-22/blocks-37-4-3-1998.json
SHA256: 0ae8ce6798238027f0326e9e7adcf92b5a6f6923b5deca95f2d6a8f4ebe2209c
Provenance, including LJCR-derived filling and seeds: coverings/quadruple-assembly/sources.md. -/

set_option Elab.async false

set_option maxRecDepth 50000

set_option maxHeartbeats 10000000

namespace CoveringDesigns.QuadrupleAssembly.WitnessData.V37

def piece112 : List (Finset (Fin 37)) := [
  {8,20,26,34},
  {8,20,27,35},
  {8,21,26,35},
  {8,21,27,34},
  {9,20,26,35},
  {9,20,27,34},
  {9,21,26,34},
  {9,21,27,35}
]

theorem piece112_eq : piece112 = hPilotPiece {4,10,13,17} := by decide +kernel

def piece113 : List (Finset (Fin 37)) := [
  {8,22,24,32},
  {8,22,25,33},
  {8,23,24,33},
  {8,23,25,32},
  {9,22,24,33},
  {9,22,25,32},
  {9,23,24,32},
  {9,23,25,33}
]

theorem piece113_eq : piece113 = hPilotPiece {4,11,12,16} := by decide +kernel

def piece114 : List (Finset (Fin 37)) := [
  {10,12,20,34},
  {10,12,21,35},
  {10,13,20,35},
  {10,13,21,34},
  {11,12,20,35},
  {11,12,21,34},
  {11,13,20,34},
  {11,13,21,35}
]

theorem piece114_eq : piece114 = hPilotPiece {5,6,10,17} := by decide +kernel

def piece115 : List (Finset (Fin 37)) := [
  {10,12,22,24},
  {10,12,23,25},
  {10,13,22,25},
  {10,13,23,24},
  {11,12,22,25},
  {11,12,23,24},
  {11,13,22,24},
  {11,13,23,25}
]

theorem piece115_eq : piece115 = hPilotPiece {5,6,11,12} := by decide +kernel

def piece116 : List (Finset (Fin 37)) := [
  {10,12,26,30},
  {10,12,27,31},
  {10,13,26,31},
  {10,13,27,30},
  {11,12,26,31},
  {11,12,27,30},
  {11,13,26,30},
  {11,13,27,31}
]

theorem piece116_eq : piece116 = hPilotPiece {5,6,13,15} := by decide +kernel

def piece117 : List (Finset (Fin 37)) := [
  {10,14,18,28},
  {10,14,19,29},
  {10,15,18,29},
  {10,15,19,28},
  {11,14,18,29},
  {11,14,19,28},
  {11,15,18,28},
  {11,15,19,29}
]

theorem piece117_eq : piece117 = hPilotPiece {5,7,9,14} := by decide +kernel

def piece118 : List (Finset (Fin 37)) := [
  {10,14,22,32},
  {10,14,23,33},
  {10,15,22,33},
  {10,15,23,32},
  {11,14,22,33},
  {11,14,23,32},
  {11,15,22,32},
  {11,15,23,33}
]

theorem piece118_eq : piece118 = hPilotPiece {5,7,11,16} := by decide +kernel

def piece119 : List (Finset (Fin 37)) := [
  {10,14,24,34},
  {10,14,25,35},
  {10,15,24,35},
  {10,15,25,34},
  {11,14,24,35},
  {11,14,25,34},
  {11,15,24,34},
  {11,15,25,35}
]

theorem piece119_eq : piece119 = hPilotPiece {5,7,12,17} := by decide +kernel

def piece120 : List (Finset (Fin 37)) := [
  {10,16,18,30},
  {10,16,19,31},
  {10,17,18,31},
  {10,17,19,30},
  {11,16,18,31},
  {11,16,19,30},
  {11,17,18,30},
  {11,17,19,31}
]

theorem piece120_eq : piece120 = hPilotPiece {5,8,9,15} := by decide +kernel

def piece121 : List (Finset (Fin 37)) := [
  {10,16,20,26},
  {10,16,21,27},
  {10,17,20,27},
  {10,17,21,26},
  {11,16,20,27},
  {11,16,21,26},
  {11,17,20,26},
  {11,17,21,27}
]

theorem piece121_eq : piece121 = hPilotPiece {5,8,10,13} := by decide +kernel

def piece122 : List (Finset (Fin 37)) := [
  {10,16,28,32},
  {10,16,29,33},
  {10,17,28,33},
  {10,17,29,32},
  {11,16,28,33},
  {11,16,29,32},
  {11,17,28,32},
  {11,17,29,33}
]

theorem piece122_eq : piece122 = hPilotPiece {5,8,14,16} := by decide +kernel

def piece123 : List (Finset (Fin 37)) := [
  {10,18,26,34},
  {10,18,27,35},
  {10,19,26,35},
  {10,19,27,34},
  {11,18,26,35},
  {11,18,27,34},
  {11,19,26,34},
  {11,19,27,35}
]

theorem piece123_eq : piece123 = hPilotPiece {5,9,13,17} := by decide +kernel

def piece124 : List (Finset (Fin 37)) := [
  {10,20,24,32},
  {10,20,25,33},
  {10,21,24,33},
  {10,21,25,32},
  {11,20,24,33},
  {11,20,25,32},
  {11,21,24,32},
  {11,21,25,33}
]

theorem piece124_eq : piece124 = hPilotPiece {5,10,12,16} := by decide +kernel

def piece125 : List (Finset (Fin 37)) := [
  {10,22,28,30},
  {10,22,29,31},
  {10,23,28,31},
  {10,23,29,30},
  {11,22,28,31},
  {11,22,29,30},
  {11,23,28,30},
  {11,23,29,31}
]

theorem piece125_eq : piece125 = hPilotPiece {5,11,14,15} := by decide +kernel

def piece126 : List (Finset (Fin 37)) := [
  {12,18,24,30},
  {12,18,25,31},
  {12,19,24,31},
  {12,19,25,30},
  {13,18,24,31},
  {13,18,25,30},
  {13,19,24,30},
  {13,19,25,31}
]

theorem piece126_eq : piece126 = hPilotPiece {6,9,12,15} := by decide +kernel

def piece127 : List (Finset (Fin 37)) := [
  {12,18,26,32},
  {12,18,27,33},
  {12,19,26,33},
  {12,19,27,32},
  {13,18,26,33},
  {13,18,27,32},
  {13,19,26,32},
  {13,19,27,33}
]

theorem piece127_eq : piece127 = hPilotPiece {6,9,13,16} := by decide +kernel

def piece128 : List (Finset (Fin 37)) := [
  {12,18,28,34},
  {12,18,29,35},
  {12,19,28,35},
  {12,19,29,34},
  {13,18,28,35},
  {13,18,29,34},
  {13,19,28,34},
  {13,19,29,35}
]

theorem piece128_eq : piece128 = hPilotPiece {6,9,14,17} := by decide +kernel

def piece129 : List (Finset (Fin 37)) := [
  {14,20,24,30},
  {14,20,25,31},
  {14,21,24,31},
  {14,21,25,30},
  {15,20,24,31},
  {15,20,25,30},
  {15,21,24,30},
  {15,21,25,31}
]

theorem piece129_eq : piece129 = hPilotPiece {7,10,12,15} := by decide +kernel

def piece130 : List (Finset (Fin 37)) := [
  {14,20,26,32},
  {14,20,27,33},
  {14,21,26,33},
  {14,21,27,32},
  {15,20,26,33},
  {15,20,27,32},
  {15,21,26,32},
  {15,21,27,33}
]

theorem piece130_eq : piece130 = hPilotPiece {7,10,13,16} := by decide +kernel

def piece131 : List (Finset (Fin 37)) := [
  {14,20,28,34},
  {14,20,29,35},
  {14,21,28,35},
  {14,21,29,34},
  {15,20,28,35},
  {15,20,29,34},
  {15,21,28,34},
  {15,21,29,35}
]

theorem piece131_eq : piece131 = hPilotPiece {7,10,14,17} := by decide +kernel

def piece132 : List (Finset (Fin 37)) := [
  {16,22,24,30},
  {16,22,25,31},
  {16,23,24,31},
  {16,23,25,30},
  {17,22,24,31},
  {17,22,25,30},
  {17,23,24,30},
  {17,23,25,31}
]

theorem piece132_eq : piece132 = hPilotPiece {8,11,12,15} := by decide +kernel

def piece133 : List (Finset (Fin 37)) := [
  {16,22,26,32},
  {16,22,27,33},
  {16,23,26,33},
  {16,23,27,32},
  {17,22,26,33},
  {17,22,27,32},
  {17,23,26,32},
  {17,23,27,33}
]

theorem piece133_eq : piece133 = hPilotPiece {8,11,13,16} := by decide +kernel

def piece134 : List (Finset (Fin 37)) := [
  {16,22,28,34},
  {16,22,29,35},
  {16,23,28,35},
  {16,23,29,34},
  {17,22,28,35},
  {17,22,29,34},
  {17,23,28,34},
  {17,23,29,35}
]

theorem piece134_eq : piece134 = hPilotPiece {8,11,14,17} := by decide +kernel

def piece135 : List (Finset (Fin 37)) := [
  {0,12,24,36}
]

theorem piece135_eq : piece135 = [gPilotPiece {0,12,24}] := by decide +kernel

def piece136 : List (Finset (Fin 37)) := [
  {0,13,25,36}
]

theorem piece136_eq : piece136 = [gPilotPiece {0,13,25}] := by decide +kernel

def piece137 : List (Finset (Fin 37)) := [
  {0,14,26,36}
]

theorem piece137_eq : piece137 = [gPilotPiece {0,14,26}] := by decide +kernel

def piece138 : List (Finset (Fin 37)) := [
  {0,15,27,36}
]

theorem piece138_eq : piece138 = [gPilotPiece {0,15,27}] := by decide +kernel

def piece139 : List (Finset (Fin 37)) := [
  {0,16,28,36}
]

theorem piece139_eq : piece139 = [gPilotPiece {0,16,28}] := by decide +kernel

def piece140 : List (Finset (Fin 37)) := [
  {0,17,29,36}
]

theorem piece140_eq : piece140 = [gPilotPiece {0,17,29}] := by decide +kernel

def piece141 : List (Finset (Fin 37)) := [
  {0,18,30,36}
]

theorem piece141_eq : piece141 = [gPilotPiece {0,18,30}] := by decide +kernel

def piece142 : List (Finset (Fin 37)) := [
  {0,19,31,36}
]

theorem piece142_eq : piece142 = [gPilotPiece {0,19,31}] := by decide +kernel

def piece143 : List (Finset (Fin 37)) := [
  {0,20,32,36}
]

theorem piece143_eq : piece143 = [gPilotPiece {0,20,32}] := by decide +kernel

def piece144 : List (Finset (Fin 37)) := [
  {0,21,33,36}
]

theorem piece144_eq : piece144 = [gPilotPiece {0,21,33}] := by decide +kernel

def piece145 : List (Finset (Fin 37)) := [
  {0,22,34,36}
]

theorem piece145_eq : piece145 = [gPilotPiece {0,22,34}] := by decide +kernel

def piece146 : List (Finset (Fin 37)) := [
  {0,23,35,36}
]

theorem piece146_eq : piece146 = [gPilotPiece {0,23,35}] := by decide +kernel

def piece147 : List (Finset (Fin 37)) := [
  {1,12,25,36}
]

theorem piece147_eq : piece147 = [gPilotPiece {1,12,25}] := by decide +kernel

def piece148 : List (Finset (Fin 37)) := [
  {1,13,26,36}
]

theorem piece148_eq : piece148 = [gPilotPiece {1,13,26}] := by decide +kernel

def piece149 : List (Finset (Fin 37)) := [
  {1,14,27,36}
]

theorem piece149_eq : piece149 = [gPilotPiece {1,14,27}] := by decide +kernel

def piece150 : List (Finset (Fin 37)) := [
  {1,15,28,36}
]

theorem piece150_eq : piece150 = [gPilotPiece {1,15,28}] := by decide +kernel

def piece151 : List (Finset (Fin 37)) := [
  {1,16,29,36}
]

theorem piece151_eq : piece151 = [gPilotPiece {1,16,29}] := by decide +kernel

def piece152 : List (Finset (Fin 37)) := [
  {1,17,30,36}
]

theorem piece152_eq : piece152 = [gPilotPiece {1,17,30}] := by decide +kernel

def piece153 : List (Finset (Fin 37)) := [
  {1,18,31,36}
]

theorem piece153_eq : piece153 = [gPilotPiece {1,18,31}] := by decide +kernel

def piece154 : List (Finset (Fin 37)) := [
  {1,19,32,36}
]

theorem piece154_eq : piece154 = [gPilotPiece {1,19,32}] := by decide +kernel

def piece155 : List (Finset (Fin 37)) := [
  {1,20,33,36}
]

theorem piece155_eq : piece155 = [gPilotPiece {1,20,33}] := by decide +kernel

def piece156 : List (Finset (Fin 37)) := [
  {1,21,34,36}
]

theorem piece156_eq : piece156 = [gPilotPiece {1,21,34}] := by decide +kernel

def piece157 : List (Finset (Fin 37)) := [
  {1,22,35,36}
]

theorem piece157_eq : piece157 = [gPilotPiece {1,22,35}] := by decide +kernel

def piece158 : List (Finset (Fin 37)) := [
  {1,23,24,36}
]

theorem piece158_eq : piece158 = [gPilotPiece {1,23,24}] := by decide +kernel

def piece159 : List (Finset (Fin 37)) := [
  {2,12,26,36}
]

theorem piece159_eq : piece159 = [gPilotPiece {2,12,26}] := by decide +kernel

def piece160 : List (Finset (Fin 37)) := [
  {2,13,27,36}
]

theorem piece160_eq : piece160 = [gPilotPiece {2,13,27}] := by decide +kernel

def piece161 : List (Finset (Fin 37)) := [
  {2,14,28,36}
]

theorem piece161_eq : piece161 = [gPilotPiece {2,14,28}] := by decide +kernel

def piece162 : List (Finset (Fin 37)) := [
  {2,15,29,36}
]

theorem piece162_eq : piece162 = [gPilotPiece {2,15,29}] := by decide +kernel

def piece163 : List (Finset (Fin 37)) := [
  {2,16,30,36}
]

theorem piece163_eq : piece163 = [gPilotPiece {2,16,30}] := by decide +kernel

def piece164 : List (Finset (Fin 37)) := [
  {2,17,31,36}
]

theorem piece164_eq : piece164 = [gPilotPiece {2,17,31}] := by decide +kernel

def piece165 : List (Finset (Fin 37)) := [
  {2,18,32,36}
]

theorem piece165_eq : piece165 = [gPilotPiece {2,18,32}] := by decide +kernel

def piece166 : List (Finset (Fin 37)) := [
  {2,19,33,36}
]

theorem piece166_eq : piece166 = [gPilotPiece {2,19,33}] := by decide +kernel

def piece167 : List (Finset (Fin 37)) := [
  {2,20,34,36}
]

theorem piece167_eq : piece167 = [gPilotPiece {2,20,34}] := by decide +kernel

def piece168 : List (Finset (Fin 37)) := [
  {2,21,35,36}
]

theorem piece168_eq : piece168 = [gPilotPiece {2,21,35}] := by decide +kernel

def piece169 : List (Finset (Fin 37)) := [
  {2,22,24,36}
]

theorem piece169_eq : piece169 = [gPilotPiece {2,22,24}] := by decide +kernel

def piece170 : List (Finset (Fin 37)) := [
  {2,23,25,36}
]

theorem piece170_eq : piece170 = [gPilotPiece {2,23,25}] := by decide +kernel

def piece171 : List (Finset (Fin 37)) := [
  {3,12,27,36}
]

theorem piece171_eq : piece171 = [gPilotPiece {3,12,27}] := by decide +kernel

def piece172 : List (Finset (Fin 37)) := [
  {3,13,28,36}
]

theorem piece172_eq : piece172 = [gPilotPiece {3,13,28}] := by decide +kernel

def piece173 : List (Finset (Fin 37)) := [
  {3,14,29,36}
]

theorem piece173_eq : piece173 = [gPilotPiece {3,14,29}] := by decide +kernel

def piece174 : List (Finset (Fin 37)) := [
  {3,15,30,36}
]

theorem piece174_eq : piece174 = [gPilotPiece {3,15,30}] := by decide +kernel

def piece175 : List (Finset (Fin 37)) := [
  {3,16,31,36}
]

theorem piece175_eq : piece175 = [gPilotPiece {3,16,31}] := by decide +kernel

def piece176 : List (Finset (Fin 37)) := [
  {3,17,32,36}
]

theorem piece176_eq : piece176 = [gPilotPiece {3,17,32}] := by decide +kernel

def piece177 : List (Finset (Fin 37)) := [
  {3,18,33,36}
]

theorem piece177_eq : piece177 = [gPilotPiece {3,18,33}] := by decide +kernel

def piece178 : List (Finset (Fin 37)) := [
  {3,19,34,36}
]

theorem piece178_eq : piece178 = [gPilotPiece {3,19,34}] := by decide +kernel

def piece179 : List (Finset (Fin 37)) := [
  {3,20,35,36}
]

theorem piece179_eq : piece179 = [gPilotPiece {3,20,35}] := by decide +kernel

def piece180 : List (Finset (Fin 37)) := [
  {3,21,24,36}
]

theorem piece180_eq : piece180 = [gPilotPiece {3,21,24}] := by decide +kernel

def piece181 : List (Finset (Fin 37)) := [
  {3,22,25,36}
]

theorem piece181_eq : piece181 = [gPilotPiece {3,22,25}] := by decide +kernel

def piece182 : List (Finset (Fin 37)) := [
  {3,23,26,36}
]

theorem piece182_eq : piece182 = [gPilotPiece {3,23,26}] := by decide +kernel

def piece183 : List (Finset (Fin 37)) := [
  {4,12,28,36}
]

theorem piece183_eq : piece183 = [gPilotPiece {4,12,28}] := by decide +kernel

def piece184 : List (Finset (Fin 37)) := [
  {4,13,29,36}
]

theorem piece184_eq : piece184 = [gPilotPiece {4,13,29}] := by decide +kernel

def piece185 : List (Finset (Fin 37)) := [
  {4,14,30,36}
]

theorem piece185_eq : piece185 = [gPilotPiece {4,14,30}] := by decide +kernel

def piece186 : List (Finset (Fin 37)) := [
  {4,15,31,36}
]

theorem piece186_eq : piece186 = [gPilotPiece {4,15,31}] := by decide +kernel

def piece187 : List (Finset (Fin 37)) := [
  {4,16,32,36}
]

theorem piece187_eq : piece187 = [gPilotPiece {4,16,32}] := by decide +kernel

def piece188 : List (Finset (Fin 37)) := [
  {4,17,33,36}
]

theorem piece188_eq : piece188 = [gPilotPiece {4,17,33}] := by decide +kernel

def piece189 : List (Finset (Fin 37)) := [
  {4,18,34,36}
]

theorem piece189_eq : piece189 = [gPilotPiece {4,18,34}] := by decide +kernel

def piece190 : List (Finset (Fin 37)) := [
  {4,19,35,36}
]

theorem piece190_eq : piece190 = [gPilotPiece {4,19,35}] := by decide +kernel

def piece191 : List (Finset (Fin 37)) := [
  {4,20,24,36}
]

theorem piece191_eq : piece191 = [gPilotPiece {4,20,24}] := by decide +kernel

def piece192 : List (Finset (Fin 37)) := [
  {4,21,25,36}
]

theorem piece192_eq : piece192 = [gPilotPiece {4,21,25}] := by decide +kernel

def piece193 : List (Finset (Fin 37)) := [
  {4,22,26,36}
]

theorem piece193_eq : piece193 = [gPilotPiece {4,22,26}] := by decide +kernel

def piece194 : List (Finset (Fin 37)) := [
  {4,23,27,36}
]

theorem piece194_eq : piece194 = [gPilotPiece {4,23,27}] := by decide +kernel

def piece195 : List (Finset (Fin 37)) := [
  {5,12,29,36}
]

theorem piece195_eq : piece195 = [gPilotPiece {5,12,29}] := by decide +kernel

def piece196 : List (Finset (Fin 37)) := [
  {5,13,30,36}
]

theorem piece196_eq : piece196 = [gPilotPiece {5,13,30}] := by decide +kernel

def piece197 : List (Finset (Fin 37)) := [
  {5,14,31,36}
]

theorem piece197_eq : piece197 = [gPilotPiece {5,14,31}] := by decide +kernel

def piece198 : List (Finset (Fin 37)) := [
  {5,15,32,36}
]

theorem piece198_eq : piece198 = [gPilotPiece {5,15,32}] := by decide +kernel

def piece199 : List (Finset (Fin 37)) := [
  {5,16,33,36}
]

theorem piece199_eq : piece199 = [gPilotPiece {5,16,33}] := by decide +kernel

def piece200 : List (Finset (Fin 37)) := [
  {5,17,34,36}
]

theorem piece200_eq : piece200 = [gPilotPiece {5,17,34}] := by decide +kernel

def piece201 : List (Finset (Fin 37)) := [
  {5,18,35,36}
]

theorem piece201_eq : piece201 = [gPilotPiece {5,18,35}] := by decide +kernel

def piece202 : List (Finset (Fin 37)) := [
  {5,19,24,36}
]

theorem piece202_eq : piece202 = [gPilotPiece {5,19,24}] := by decide +kernel

def piece203 : List (Finset (Fin 37)) := [
  {5,20,25,36}
]

theorem piece203_eq : piece203 = [gPilotPiece {5,20,25}] := by decide +kernel

def piece204 : List (Finset (Fin 37)) := [
  {5,21,26,36}
]

theorem piece204_eq : piece204 = [gPilotPiece {5,21,26}] := by decide +kernel

def piece205 : List (Finset (Fin 37)) := [
  {5,22,27,36}
]

theorem piece205_eq : piece205 = [gPilotPiece {5,22,27}] := by decide +kernel

def piece206 : List (Finset (Fin 37)) := [
  {5,23,28,36}
]

theorem piece206_eq : piece206 = [gPilotPiece {5,23,28}] := by decide +kernel

def piece207 : List (Finset (Fin 37)) := [
  {6,12,30,36}
]

theorem piece207_eq : piece207 = [gPilotPiece {6,12,30}] := by decide +kernel

def piece208 : List (Finset (Fin 37)) := [
  {6,13,31,36}
]

theorem piece208_eq : piece208 = [gPilotPiece {6,13,31}] := by decide +kernel

def piece209 : List (Finset (Fin 37)) := [
  {6,14,32,36}
]

theorem piece209_eq : piece209 = [gPilotPiece {6,14,32}] := by decide +kernel

def piece210 : List (Finset (Fin 37)) := [
  {6,15,33,36}
]

theorem piece210_eq : piece210 = [gPilotPiece {6,15,33}] := by decide +kernel

def piece211 : List (Finset (Fin 37)) := [
  {6,16,34,36}
]

theorem piece211_eq : piece211 = [gPilotPiece {6,16,34}] := by decide +kernel

def piece212 : List (Finset (Fin 37)) := [
  {6,17,35,36}
]

theorem piece212_eq : piece212 = [gPilotPiece {6,17,35}] := by decide +kernel

def piece213 : List (Finset (Fin 37)) := [
  {6,18,24,36}
]

theorem piece213_eq : piece213 = [gPilotPiece {6,18,24}] := by decide +kernel

def piece214 : List (Finset (Fin 37)) := [
  {6,19,25,36}
]

theorem piece214_eq : piece214 = [gPilotPiece {6,19,25}] := by decide +kernel

def piece215 : List (Finset (Fin 37)) := [
  {6,20,26,36}
]

theorem piece215_eq : piece215 = [gPilotPiece {6,20,26}] := by decide +kernel

def piece216 : List (Finset (Fin 37)) := [
  {6,21,27,36}
]

theorem piece216_eq : piece216 = [gPilotPiece {6,21,27}] := by decide +kernel

def piece217 : List (Finset (Fin 37)) := [
  {6,22,28,36}
]

theorem piece217_eq : piece217 = [gPilotPiece {6,22,28}] := by decide +kernel

def piece218 : List (Finset (Fin 37)) := [
  {6,23,29,36}
]

theorem piece218_eq : piece218 = [gPilotPiece {6,23,29}] := by decide +kernel

def piece219 : List (Finset (Fin 37)) := [
  {7,12,31,36}
]

theorem piece219_eq : piece219 = [gPilotPiece {7,12,31}] := by decide +kernel

def piece220 : List (Finset (Fin 37)) := [
  {7,13,32,36}
]

theorem piece220_eq : piece220 = [gPilotPiece {7,13,32}] := by decide +kernel

def piece221 : List (Finset (Fin 37)) := [
  {7,14,33,36}
]

theorem piece221_eq : piece221 = [gPilotPiece {7,14,33}] := by decide +kernel

def piece222 : List (Finset (Fin 37)) := [
  {7,15,34,36}
]

theorem piece222_eq : piece222 = [gPilotPiece {7,15,34}] := by decide +kernel

def piece223 : List (Finset (Fin 37)) := [
  {7,16,35,36}
]

theorem piece223_eq : piece223 = [gPilotPiece {7,16,35}] := by decide +kernel

def piece224 : List (Finset (Fin 37)) := [
  {7,17,24,36}
]

theorem piece224_eq : piece224 = [gPilotPiece {7,17,24}] := by decide +kernel

def piece225 : List (Finset (Fin 37)) := [
  {7,18,25,36}
]

theorem piece225_eq : piece225 = [gPilotPiece {7,18,25}] := by decide +kernel

def piece226 : List (Finset (Fin 37)) := [
  {7,19,26,36}
]

theorem piece226_eq : piece226 = [gPilotPiece {7,19,26}] := by decide +kernel

def piece227 : List (Finset (Fin 37)) := [
  {7,20,27,36}
]

theorem piece227_eq : piece227 = [gPilotPiece {7,20,27}] := by decide +kernel

def piece228 : List (Finset (Fin 37)) := [
  {7,21,28,36}
]

theorem piece228_eq : piece228 = [gPilotPiece {7,21,28}] := by decide +kernel

def piece229 : List (Finset (Fin 37)) := [
  {7,22,29,36}
]

theorem piece229_eq : piece229 = [gPilotPiece {7,22,29}] := by decide +kernel

def piece230 : List (Finset (Fin 37)) := [
  {7,23,30,36}
]

theorem piece230_eq : piece230 = [gPilotPiece {7,23,30}] := by decide +kernel

def piece231 : List (Finset (Fin 37)) := [
  {8,12,32,36}
]

theorem piece231_eq : piece231 = [gPilotPiece {8,12,32}] := by decide +kernel

def piece232 : List (Finset (Fin 37)) := [
  {8,13,33,36}
]

theorem piece232_eq : piece232 = [gPilotPiece {8,13,33}] := by decide +kernel

def piece233 : List (Finset (Fin 37)) := [
  {8,14,34,36}
]

theorem piece233_eq : piece233 = [gPilotPiece {8,14,34}] := by decide +kernel

def piece234 : List (Finset (Fin 37)) := [
  {8,15,35,36}
]

theorem piece234_eq : piece234 = [gPilotPiece {8,15,35}] := by decide +kernel

def piece235 : List (Finset (Fin 37)) := [
  {8,16,24,36}
]

theorem piece235_eq : piece235 = [gPilotPiece {8,16,24}] := by decide +kernel

def piece236 : List (Finset (Fin 37)) := [
  {8,17,25,36}
]

theorem piece236_eq : piece236 = [gPilotPiece {8,17,25}] := by decide +kernel

def piece237 : List (Finset (Fin 37)) := [
  {8,18,26,36}
]

theorem piece237_eq : piece237 = [gPilotPiece {8,18,26}] := by decide +kernel

def piece238 : List (Finset (Fin 37)) := [
  {8,19,27,36}
]

theorem piece238_eq : piece238 = [gPilotPiece {8,19,27}] := by decide +kernel

def piece239 : List (Finset (Fin 37)) := [
  {8,20,28,36}
]

theorem piece239_eq : piece239 = [gPilotPiece {8,20,28}] := by decide +kernel

def piece240 : List (Finset (Fin 37)) := [
  {8,21,29,36}
]

theorem piece240_eq : piece240 = [gPilotPiece {8,21,29}] := by decide +kernel

def piece241 : List (Finset (Fin 37)) := [
  {8,22,30,36}
]

theorem piece241_eq : piece241 = [gPilotPiece {8,22,30}] := by decide +kernel

def piece242 : List (Finset (Fin 37)) := [
  {8,23,31,36}
]

theorem piece242_eq : piece242 = [gPilotPiece {8,23,31}] := by decide +kernel

def piece243 : List (Finset (Fin 37)) := [
  {9,12,33,36}
]

theorem piece243_eq : piece243 = [gPilotPiece {9,12,33}] := by decide +kernel

def piece244 : List (Finset (Fin 37)) := [
  {9,13,34,36}
]

theorem piece244_eq : piece244 = [gPilotPiece {9,13,34}] := by decide +kernel

def piece245 : List (Finset (Fin 37)) := [
  {9,14,35,36}
]

theorem piece245_eq : piece245 = [gPilotPiece {9,14,35}] := by decide +kernel

def piece246 : List (Finset (Fin 37)) := [
  {9,15,24,36}
]

theorem piece246_eq : piece246 = [gPilotPiece {9,15,24}] := by decide +kernel

def piece247 : List (Finset (Fin 37)) := [
  {9,16,25,36}
]

theorem piece247_eq : piece247 = [gPilotPiece {9,16,25}] := by decide +kernel

def piece248 : List (Finset (Fin 37)) := [
  {9,17,26,36}
]

theorem piece248_eq : piece248 = [gPilotPiece {9,17,26}] := by decide +kernel

def piece249 : List (Finset (Fin 37)) := [
  {9,18,27,36}
]

theorem piece249_eq : piece249 = [gPilotPiece {9,18,27}] := by decide +kernel

def piece250 : List (Finset (Fin 37)) := [
  {9,19,28,36}
]

theorem piece250_eq : piece250 = [gPilotPiece {9,19,28}] := by decide +kernel

def piece251 : List (Finset (Fin 37)) := [
  {9,20,29,36}
]

theorem piece251_eq : piece251 = [gPilotPiece {9,20,29}] := by decide +kernel

def piece252 : List (Finset (Fin 37)) := [
  {9,21,30,36}
]

theorem piece252_eq : piece252 = [gPilotPiece {9,21,30}] := by decide +kernel

def piece253 : List (Finset (Fin 37)) := [
  {9,22,31,36}
]

theorem piece253_eq : piece253 = [gPilotPiece {9,22,31}] := by decide +kernel

def piece254 : List (Finset (Fin 37)) := [
  {9,23,32,36}
]

theorem piece254_eq : piece254 = [gPilotPiece {9,23,32}] := by decide +kernel

def piece255 : List (Finset (Fin 37)) := [
  {10,12,34,36}
]

theorem piece255_eq : piece255 = [gPilotPiece {10,12,34}] := by decide +kernel

def piece256 : List (Finset (Fin 37)) := [
  {10,13,35,36}
]

theorem piece256_eq : piece256 = [gPilotPiece {10,13,35}] := by decide +kernel

def piece257 : List (Finset (Fin 37)) := [
  {10,14,24,36}
]

theorem piece257_eq : piece257 = [gPilotPiece {10,14,24}] := by decide +kernel

def piece258 : List (Finset (Fin 37)) := [
  {10,15,25,36}
]

theorem piece258_eq : piece258 = [gPilotPiece {10,15,25}] := by decide +kernel

def piece259 : List (Finset (Fin 37)) := [
  {10,16,26,36}
]

theorem piece259_eq : piece259 = [gPilotPiece {10,16,26}] := by decide +kernel

def piece260 : List (Finset (Fin 37)) := [
  {10,17,27,36}
]

theorem piece260_eq : piece260 = [gPilotPiece {10,17,27}] := by decide +kernel

def piece261 : List (Finset (Fin 37)) := [
  {10,18,28,36}
]

theorem piece261_eq : piece261 = [gPilotPiece {10,18,28}] := by decide +kernel

def piece262 : List (Finset (Fin 37)) := [
  {10,19,29,36}
]

theorem piece262_eq : piece262 = [gPilotPiece {10,19,29}] := by decide +kernel

def piece263 : List (Finset (Fin 37)) := [
  {10,20,30,36}
]

theorem piece263_eq : piece263 = [gPilotPiece {10,20,30}] := by decide +kernel

def piece264 : List (Finset (Fin 37)) := [
  {10,21,31,36}
]

theorem piece264_eq : piece264 = [gPilotPiece {10,21,31}] := by decide +kernel

def piece265 : List (Finset (Fin 37)) := [
  {10,22,32,36}
]

theorem piece265_eq : piece265 = [gPilotPiece {10,22,32}] := by decide +kernel

def piece266 : List (Finset (Fin 37)) := [
  {10,23,33,36}
]

theorem piece266_eq : piece266 = [gPilotPiece {10,23,33}] := by decide +kernel

def piece267 : List (Finset (Fin 37)) := [
  {11,12,35,36}
]

theorem piece267_eq : piece267 = [gPilotPiece {11,12,35}] := by decide +kernel

def piece268 : List (Finset (Fin 37)) := [
  {11,13,24,36}
]

theorem piece268_eq : piece268 = [gPilotPiece {11,13,24}] := by decide +kernel

def piece269 : List (Finset (Fin 37)) := [
  {11,14,25,36}
]

theorem piece269_eq : piece269 = [gPilotPiece {11,14,25}] := by decide +kernel

def piece270 : List (Finset (Fin 37)) := [
  {11,15,26,36}
]

theorem piece270_eq : piece270 = [gPilotPiece {11,15,26}] := by decide +kernel

def piece271 : List (Finset (Fin 37)) := [
  {11,16,27,36}
]

theorem piece271_eq : piece271 = [gPilotPiece {11,16,27}] := by decide +kernel

def piece272 : List (Finset (Fin 37)) := [
  {11,17,28,36}
]

theorem piece272_eq : piece272 = [gPilotPiece {11,17,28}] := by decide +kernel

def piece273 : List (Finset (Fin 37)) := [
  {11,18,29,36}
]

theorem piece273_eq : piece273 = [gPilotPiece {11,18,29}] := by decide +kernel

def piece274 : List (Finset (Fin 37)) := [
  {11,19,30,36}
]

theorem piece274_eq : piece274 = [gPilotPiece {11,19,30}] := by decide +kernel

def piece275 : List (Finset (Fin 37)) := [
  {11,20,31,36}
]

theorem piece275_eq : piece275 = [gPilotPiece {11,20,31}] := by decide +kernel

def piece276 : List (Finset (Fin 37)) := [
  {11,21,32,36}
]

theorem piece276_eq : piece276 = [gPilotPiece {11,21,32}] := by decide +kernel

def piece277 : List (Finset (Fin 37)) := [
  {11,22,33,36}
]

theorem piece277_eq : piece277 = [gPilotPiece {11,22,33}] := by decide +kernel

def piece278 : List (Finset (Fin 37)) := [
  {11,23,34,36}
]

theorem piece278_eq : piece278 = [gPilotPiece {11,23,34}] := by decide +kernel

def piece279 : List (Finset (Fin 37)) := [
  {0,1,2,4},
  {0,1,3,4},
  {0,1,5,7},
  {0,1,6,8},
  {0,1,9,36},
  {0,1,10,11},
  {0,2,3,8},
  {0,2,5,8},
  {0,2,6,11},
  {0,2,7,9},
  {0,2,10,36},
  {0,3,5,10},
  {0,3,6,36},
  {0,3,7,36},
  {0,3,9,11},
  {0,4,5,7},
  {0,4,6,11},
  {0,4,8,36},
  {0,4,9,10},
  {0,5,6,9},
  {0,5,11,36},
  {0,6,7,10},
  {0,7,8,11},
  {0,8,9,10},
  {1,2,3,36},
  {1,2,5,6},
  {1,2,5,11},
  {1,2,7,9},
  {1,2,8,10},
  {1,3,5,9},
  {1,3,6,8},
  {1,3,7,11},
  {1,3,9,10},
  {1,4,5,8},
  {1,4,6,9},
  {1,4,7,36},
  {1,4,10,11},
  {1,5,10,36},
  {1,6,7,10},
  {1,6,11,36},
  {1,7,8,36},
  {1,8,9,11},
  {2,3,4,11},
  {2,3,5,7},
  {2,3,6,9},
  {2,3,6,10},
  {2,4,5,10},
  {2,4,6,36},
  {2,4,7,10},
  {2,4,8,9},
  {2,5,9,36},
  {2,6,7,8},
  {2,7,11,36},
  {2,8,11,36},
  {2,9,10,11},
  {3,4,5,36},
  {3,4,6,7},
  {3,4,7,9},
  {3,4,8,10},
  {3,5,6,11},
  {3,5,8,11},
  {3,7,8,10},
  {3,8,9,36},
  {3,10,11,36},
  {4,5,6,8},
  {4,5,9,11},
  {4,6,10,36},
  {4,7,8,11},
  {4,9,11,36},
  {5,6,7,36},
  {5,6,9,10},
  {5,7,8,9},
  {5,7,10,11},
  {5,8,10,36},
  {6,7,9,11},
  {6,8,9,36},
  {6,8,10,11},
  {7,9,10,36}
]

theorem piece279_eq : piece279 = cPiece (u := 3) 0 := by decide +kernel

def piece280 : List (Finset (Fin 37)) := [
  {12,13,14,16},
  {12,13,15,16},
  {12,13,17,19},
  {12,13,18,20},
  {12,13,21,36},
  {12,13,22,23},
  {12,14,15,20},
  {12,14,17,20},
  {12,14,18,23},
  {12,14,19,21},
  {12,14,22,36},
  {12,15,17,22},
  {12,15,18,36},
  {12,15,19,36},
  {12,15,21,23},
  {12,16,17,19},
  {12,16,18,23},
  {12,16,20,36},
  {12,16,21,22},
  {12,17,18,21},
  {12,17,23,36},
  {12,18,19,22},
  {12,19,20,23},
  {12,20,21,22},
  {13,14,15,36},
  {13,14,17,18},
  {13,14,17,23},
  {13,14,19,21},
  {13,14,20,22},
  {13,15,17,21},
  {13,15,18,20},
  {13,15,19,23},
  {13,15,21,22},
  {13,16,17,20},
  {13,16,18,21},
  {13,16,19,36},
  {13,16,22,23},
  {13,17,22,36},
  {13,18,19,22},
  {13,18,23,36},
  {13,19,20,36},
  {13,20,21,23},
  {14,15,16,23},
  {14,15,17,19},
  {14,15,18,21},
  {14,15,18,22},
  {14,16,17,22},
  {14,16,18,36},
  {14,16,19,22},
  {14,16,20,21},
  {14,17,21,36},
  {14,18,19,20},
  {14,19,23,36},
  {14,20,23,36},
  {14,21,22,23},
  {15,16,17,36},
  {15,16,18,19},
  {15,16,19,21},
  {15,16,20,22},
  {15,17,18,23},
  {15,17,20,23},
  {15,19,20,22},
  {15,20,21,36},
  {15,22,23,36},
  {16,17,18,20},
  {16,17,21,23},
  {16,18,22,36},
  {16,19,20,23},
  {16,21,23,36},
  {17,18,19,36},
  {17,18,21,22},
  {17,19,20,21},
  {17,19,22,23},
  {17,20,22,36},
  {18,19,21,23},
  {18,20,21,36},
  {18,20,22,23},
  {19,21,22,36}
]

theorem piece280_eq : piece280 = cPiece (u := 3) 1 := by decide +kernel

def piece281 : List (Finset (Fin 37)) := [
  {24,25,26,28},
  {24,25,27,28},
  {24,25,29,31},
  {24,25,30,32},
  {24,25,33,36},
  {24,25,34,35},
  {24,26,27,32},
  {24,26,29,32},
  {24,26,30,35},
  {24,26,31,33},
  {24,26,34,36},
  {24,27,29,34},
  {24,27,30,36},
  {24,27,31,36},
  {24,27,33,35},
  {24,28,29,31},
  {24,28,30,35},
  {24,28,32,36},
  {24,28,33,34},
  {24,29,30,33},
  {24,29,35,36},
  {24,30,31,34},
  {24,31,32,35},
  {24,32,33,34},
  {25,26,27,36},
  {25,26,29,30},
  {25,26,29,35},
  {25,26,31,33},
  {25,26,32,34},
  {25,27,29,33},
  {25,27,30,32},
  {25,27,31,35},
  {25,27,33,34},
  {25,28,29,32},
  {25,28,30,33},
  {25,28,31,36},
  {25,28,34,35},
  {25,29,34,36},
  {25,30,31,34},
  {25,30,35,36},
  {25,31,32,36},
  {25,32,33,35},
  {26,27,28,35},
  {26,27,29,31},
  {26,27,30,33},
  {26,27,30,34},
  {26,28,29,34},
  {26,28,30,36},
  {26,28,31,34},
  {26,28,32,33},
  {26,29,33,36},
  {26,30,31,32},
  {26,31,35,36},
  {26,32,35,36},
  {26,33,34,35},
  {27,28,29,36},
  {27,28,30,31},
  {27,28,31,33},
  {27,28,32,34},
  {27,29,30,35},
  {27,29,32,35},
  {27,31,32,34},
  {27,32,33,36},
  {27,34,35,36},
  {28,29,30,32},
  {28,29,33,35},
  {28,30,34,36},
  {28,31,32,35},
  {28,33,35,36},
  {29,30,31,36},
  {29,30,33,34},
  {29,31,32,33},
  {29,31,34,35},
  {29,32,34,36},
  {30,31,33,35},
  {30,32,33,36},
  {30,32,34,35},
  {31,33,34,36}
]

theorem piece281_eq : piece281 = cPiece (u := 3) 2 := by decide +kernel

def piece282 : List (Finset (Fin 37)) := [
  {0,5,12,17},
  {0,5,13,16},
  {0,5,14,15},
  {1,4,12,17},
  {1,4,13,16},
  {1,4,14,15},
  {2,3,12,17},
  {2,3,13,16},
  {2,3,14,15},
  {1,5,13,17},
  {1,5,12,14},
  {1,5,15,16},
  {0,2,13,17},
  {0,2,12,14},
  {0,2,15,16},
  {3,4,13,17},
  {3,4,12,14},
  {3,4,15,16},
  {2,5,14,17},
  {2,5,13,15},
  {2,5,12,16},
  {1,3,14,17},
  {1,3,13,15},
  {1,3,12,16},
  {0,4,14,17},
  {0,4,13,15},
  {0,4,12,16},
  {3,5,15,17},
  {3,5,14,16},
  {3,5,12,13},
  {2,4,15,17},
  {2,4,14,16},
  {2,4,12,13},
  {0,1,15,17},
  {0,1,14,16},
  {0,1,12,13},
  {4,5,16,17},
  {4,5,12,15},
  {4,5,13,14},
  {0,3,16,17},
  {0,3,12,15},
  {0,3,13,14},
  {1,2,16,17},
  {1,2,12,15},
  {1,2,13,14}
]

theorem piece282_eq : piece282 = labelledDPiece (u := 3) 0 1 0 0 := by decide +kernel

def piece283 : List (Finset (Fin 37)) := [
  {0,5,18,23},
  {0,5,19,22},
  {0,5,20,21},
  {1,4,18,23},
  {1,4,19,22},
  {1,4,20,21},
  {2,3,18,23},
  {2,3,19,22},
  {2,3,20,21},
  {1,5,19,23},
  {1,5,18,20},
  {1,5,21,22},
  {0,2,19,23},
  {0,2,18,20},
  {0,2,21,22},
  {3,4,19,23},
  {3,4,18,20},
  {3,4,21,22},
  {2,5,20,23},
  {2,5,19,21},
  {2,5,18,22},
  {1,3,20,23},
  {1,3,19,21},
  {1,3,18,22},
  {0,4,20,23},
  {0,4,19,21},
  {0,4,18,22},
  {3,5,21,23},
  {3,5,20,22},
  {3,5,18,19},
  {2,4,21,23},
  {2,4,20,22},
  {2,4,18,19},
  {0,1,21,23},
  {0,1,20,22},
  {0,1,18,19},
  {4,5,22,23},
  {4,5,18,21},
  {4,5,19,20},
  {0,3,22,23},
  {0,3,18,21},
  {0,3,19,20},
  {1,2,22,23},
  {1,2,18,21},
  {1,2,19,20}
]

theorem piece283_eq : piece283 = labelledDPiece (u := 3) 0 1 0 1 := by decide +kernel

def piece284 : List (Finset (Fin 37)) := [
  {6,11,12,17},
  {6,11,13,16},
  {6,11,14,15},
  {7,10,12,17},
  {7,10,13,16},
  {7,10,14,15},
  {8,9,12,17},
  {8,9,13,16},
  {8,9,14,15},
  {7,11,13,17},
  {7,11,12,14},
  {7,11,15,16},
  {6,8,13,17},
  {6,8,12,14},
  {6,8,15,16},
  {9,10,13,17},
  {9,10,12,14},
  {9,10,15,16},
  {8,11,14,17},
  {8,11,13,15},
  {8,11,12,16},
  {7,9,14,17},
  {7,9,13,15},
  {7,9,12,16},
  {6,10,14,17},
  {6,10,13,15},
  {6,10,12,16},
  {9,11,15,17},
  {9,11,14,16},
  {9,11,12,13},
  {8,10,15,17},
  {8,10,14,16},
  {8,10,12,13},
  {6,7,15,17},
  {6,7,14,16},
  {6,7,12,13},
  {10,11,16,17},
  {10,11,12,15},
  {10,11,13,14},
  {6,9,16,17},
  {6,9,12,15},
  {6,9,13,14},
  {7,8,16,17},
  {7,8,12,15},
  {7,8,13,14}
]

theorem piece284_eq : piece284 = labelledDPiece (u := 3) 0 1 1 0 := by decide +kernel

def piece285 : List (Finset (Fin 37)) := [
  {6,11,18,23},
  {6,11,19,22},
  {6,11,20,21},
  {7,10,18,23},
  {7,10,19,22},
  {7,10,20,21},
  {8,9,18,23},
  {8,9,19,22},
  {8,9,20,21},
  {7,11,19,23},
  {7,11,18,20},
  {7,11,21,22},
  {6,8,19,23},
  {6,8,18,20},
  {6,8,21,22},
  {9,10,19,23},
  {9,10,18,20},
  {9,10,21,22},
  {8,11,20,23},
  {8,11,19,21},
  {8,11,18,22},
  {7,9,20,23},
  {7,9,19,21},
  {7,9,18,22},
  {6,10,20,23},
  {6,10,19,21},
  {6,10,18,22},
  {9,11,21,23},
  {9,11,20,22},
  {9,11,18,19},
  {8,10,21,23},
  {8,10,20,22},
  {8,10,18,19},
  {6,7,21,23},
  {6,7,20,22},
  {6,7,18,19},
  {10,11,22,23},
  {10,11,18,21},
  {10,11,19,20},
  {6,9,22,23},
  {6,9,18,21},
  {6,9,19,20},
  {7,8,22,23},
  {7,8,18,21},
  {7,8,19,20}
]

theorem piece285_eq : piece285 = labelledDPiece (u := 3) 0 1 1 1 := by decide +kernel

def piece286 : List (Finset (Fin 37)) := [
  {0,5,24,29},
  {0,5,25,28},
  {0,5,26,27},
  {1,4,24,29},
  {1,4,25,28},
  {1,4,26,27},
  {2,3,24,29},
  {2,3,25,28},
  {2,3,26,27},
  {1,5,25,29},
  {1,5,24,26},
  {1,5,27,28},
  {0,2,25,29},
  {0,2,24,26},
  {0,2,27,28},
  {3,4,25,29},
  {3,4,24,26},
  {3,4,27,28},
  {2,5,26,29},
  {2,5,25,27},
  {2,5,24,28},
  {1,3,26,29},
  {1,3,25,27},
  {1,3,24,28},
  {0,4,26,29},
  {0,4,25,27},
  {0,4,24,28},
  {3,5,27,29},
  {3,5,26,28},
  {3,5,24,25},
  {2,4,27,29},
  {2,4,26,28},
  {2,4,24,25},
  {0,1,27,29},
  {0,1,26,28},
  {0,1,24,25},
  {4,5,28,29},
  {4,5,24,27},
  {4,5,25,26},
  {0,3,28,29},
  {0,3,24,27},
  {0,3,25,26},
  {1,2,28,29},
  {1,2,24,27},
  {1,2,25,26}
]

theorem piece286_eq : piece286 = labelledDPiece (u := 3) 0 2 0 0 := by decide +kernel

def piece287 : List (Finset (Fin 37)) := [
  {0,5,30,35},
  {0,5,31,34},
  {0,5,32,33},
  {1,4,30,35},
  {1,4,31,34},
  {1,4,32,33},
  {2,3,30,35},
  {2,3,31,34},
  {2,3,32,33},
  {1,5,31,35},
  {1,5,30,32},
  {1,5,33,34},
  {0,2,31,35},
  {0,2,30,32},
  {0,2,33,34},
  {3,4,31,35},
  {3,4,30,32},
  {3,4,33,34},
  {2,5,32,35},
  {2,5,31,33},
  {2,5,30,34},
  {1,3,32,35},
  {1,3,31,33},
  {1,3,30,34},
  {0,4,32,35},
  {0,4,31,33},
  {0,4,30,34},
  {3,5,33,35},
  {3,5,32,34},
  {3,5,30,31},
  {2,4,33,35},
  {2,4,32,34},
  {2,4,30,31},
  {0,1,33,35},
  {0,1,32,34},
  {0,1,30,31},
  {4,5,34,35},
  {4,5,30,33},
  {4,5,31,32},
  {0,3,34,35},
  {0,3,30,33},
  {0,3,31,32},
  {1,2,34,35},
  {1,2,30,33},
  {1,2,31,32}
]

theorem piece287_eq : piece287 = labelledDPiece (u := 3) 0 2 0 1 := by decide +kernel

def piece288 : List (Finset (Fin 37)) := [
  {6,11,24,29},
  {6,11,25,28},
  {6,11,26,27},
  {7,10,24,29},
  {7,10,25,28},
  {7,10,26,27},
  {8,9,24,29},
  {8,9,25,28},
  {8,9,26,27},
  {7,11,25,29},
  {7,11,24,26},
  {7,11,27,28},
  {6,8,25,29},
  {6,8,24,26},
  {6,8,27,28},
  {9,10,25,29},
  {9,10,24,26},
  {9,10,27,28},
  {8,11,26,29},
  {8,11,25,27},
  {8,11,24,28},
  {7,9,26,29},
  {7,9,25,27},
  {7,9,24,28},
  {6,10,26,29},
  {6,10,25,27},
  {6,10,24,28},
  {9,11,27,29},
  {9,11,26,28},
  {9,11,24,25},
  {8,10,27,29},
  {8,10,26,28},
  {8,10,24,25},
  {6,7,27,29},
  {6,7,26,28},
  {6,7,24,25},
  {10,11,28,29},
  {10,11,24,27},
  {10,11,25,26},
  {6,9,28,29},
  {6,9,24,27},
  {6,9,25,26},
  {7,8,28,29},
  {7,8,24,27},
  {7,8,25,26}
]

theorem piece288_eq : piece288 = labelledDPiece (u := 3) 0 2 1 0 := by decide +kernel

end CoveringDesigns.QuadrupleAssembly.WitnessData.V37
