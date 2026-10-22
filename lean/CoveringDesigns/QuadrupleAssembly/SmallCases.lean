import CoveringDesigns.QuadrupleAssembly.SeedData.Filling
import CoveringDesigns.QuadrupleAssembly.WitnessData.V25
import CoveringDesigns.Foundations.Relabelling
import CoveringDesigns.Schoenheim.LowerBound

/-! The two small classical cases, separate from the u≥3 assembly.
Formalisation: Rob Gardiner, with AI assistance. The actual retained
LJCR families retain Daniel M. Gordon/LJCR attribution and CC BY 4.0 terms.
No construction at u=2 is inferred from the shared assembly's seed package. -/

namespace CoveringDesigns

namespace QuadrupleAssembly

/-- All intermediate ceilings for the thirteen-point base case. -/
theorem ceilings_13 :
    Schoenheim.ceilDiv 11 2 = 6 ∧
    Schoenheim.ceilDiv (12*6) 3 = 24 ∧
    Schoenheim.ceilDiv (13*24) 4 = 78 := by decide +kernel

/-- All intermediate ceilings for the twenty-five-point base case. -/
theorem ceilings_25 :
    Schoenheim.ceilDiv 23 2 = 12 ∧
    Schoenheim.ceilDiv (24*12) 3 = 96 ∧
    Schoenheim.ceilDiv (25*96) 4 = 600 := by decide +kernel

theorem schoenheim_13 : Schoenheim.bound 13 4 3 = 78 := by decide +kernel
theorem schoenheim_25 : Schoenheim.bound 25 4 3 = 600 := by decide +kernel

end QuadrupleAssembly

open QuadrupleAssembly

/-- This is the existing filling itself, with no second maintained copy. -/
def knownCover78_13_4_3 : Family (Fin 13) := SeedData.Filling.blocks

theorem knownCover78_13_4_3_correspondence :
    knownCover78_13_4_3 = SeedData.Filling.rows.toFinset := rfl

theorem knownCover78_13_4_3_optimal :
    IsCover knownCover78_13_4_3 4 3 ∧ knownCover78_13_4_3.card = 78 :=
  ⟨SeedData.Filling.valid, SeedData.Filling.size⟩

noncomputable def knownCover78_13_4_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 13) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover78_13_4_3

theorem knownCover78_13_4_3_on_optimal {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 13) :
    IsCover (knownCover78_13_4_3_on hv) 4 3 ∧ (knownCover78_13_4_3_on hv).card = 78 :=
  ⟨relabel_isCover _ knownCover78_13_4_3_optimal.1,
    (relabel_card _ _).trans knownCover78_13_4_3_optimal.2⟩

theorem lower_bound_13_4_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 13) (hC : IsCover C 4 3) : 78 ≤ C.card := by
  classical
  have hk : 4 ≤ Fintype.card α := by omega
  have h := Schoenheim.lower_bound (by decide : 1 ≤ 3) (by decide : 3 ≤ 4) hk hC
  simpa only [hv, schoenheim_13] using h

theorem covering_number_13_4_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 13) :
    (∃ C : Family α, IsCover C 4 3 ∧ C.card = 78) ∧
    (∀ C : Family α, IsCover C 4 3 → 78 ≤ C.card) := by
  classical
  exact ⟨⟨knownCover78_13_4_3_on hv, knownCover78_13_4_3_on_optimal hv⟩,
    fun _ hC => lower_bound_13_4_3 hv hC⟩

theorem covering_number_13_4_3 :
    (∃ C : Family (Fin 13), IsCover C 4 3 ∧ C.card = 78) ∧
    (∀ C : Family (Fin 13), IsCover C 4 3 → 78 ≤ C.card) :=
  covering_number_13_4_3_on (Fintype.card_fin 13)

/-- The projected normalized historical file, on its actual zero-based labels. -/
def knownCover600_25_4_3 : Family (Fin 25) := WitnessData.V25.blocks

theorem knownCover600_25_4_3_correspondence :
    knownCover600_25_4_3 = WitnessData.V25.rows.toFinset := rfl

theorem knownCover600_25_4_3_optimal :
    IsCover knownCover600_25_4_3 4 3 ∧ knownCover600_25_4_3.card = 600 :=
  ⟨WitnessData.V25.valid, WitnessData.V25.size⟩

noncomputable def knownCover600_25_4_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 25) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover600_25_4_3

theorem knownCover600_25_4_3_on_optimal {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 25) :
    IsCover (knownCover600_25_4_3_on hv) 4 3 ∧ (knownCover600_25_4_3_on hv).card = 600 :=
  ⟨relabel_isCover _ knownCover600_25_4_3_optimal.1,
    (relabel_card _ _).trans knownCover600_25_4_3_optimal.2⟩

theorem lower_bound_25_4_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 25) (hC : IsCover C 4 3) : 600 ≤ C.card := by
  classical
  have hk : 4 ≤ Fintype.card α := by omega
  have h := Schoenheim.lower_bound (by decide : 1 ≤ 3) (by decide : 3 ≤ 4) hk hC
  simpa only [hv, schoenheim_25] using h

theorem covering_number_25_4_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 25) :
    (∃ C : Family α, IsCover C 4 3 ∧ C.card = 600) ∧
    (∀ C : Family α, IsCover C 4 3 → 600 ≤ C.card) := by
  classical
  exact ⟨⟨knownCover600_25_4_3_on hv, knownCover600_25_4_3_on_optimal hv⟩,
    fun _ hC => lower_bound_25_4_3 hv hC⟩

theorem covering_number_25_4_3 :
    (∃ C : Family (Fin 25), IsCover C 4 3 ∧ C.card = 600) ∧
    (∀ C : Family (Fin 25), IsCover C 4 3 → 600 ≤ C.card) :=
  covering_number_25_4_3_on (Fintype.card_fin 25)

end CoveringDesigns
