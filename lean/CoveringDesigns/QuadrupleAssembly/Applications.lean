import CoveringDesigns.QuadrupleAssembly.WitnessData.V37

import CoveringDesigns.QuadrupleAssembly.WitnessData.V49

import CoveringDesigns.QuadrupleAssembly.WitnessData.V61

import CoveringDesigns.QuadrupleAssembly.WitnessData.V73

import CoveringDesigns.QuadrupleAssembly.WitnessData.V85

import CoveringDesigns.QuadrupleAssembly.WitnessData.V97

/-! Six classical exact values, reconstructed and formalised by Rob Gardiner
with AI assistance. Every attaining family is the projected distributed file. -/

namespace CoveringDesigns

open QuadrupleAssembly

def knownCover1998_37_4_3 : Family (Fin 37) := WitnessData.V37.blocks

theorem knownCover1998_37_4_3_optimal : IsCover knownCover1998_37_4_3 4 3 ∧ knownCover1998_37_4_3.card = 1998 := WitnessData.V37.optimal

noncomputable def knownCover1998_37_4_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 37) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover1998_37_4_3

theorem knownCover1998_37_4_3_on_optimal {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 37) :
    IsCover (knownCover1998_37_4_3_on hv) 4 3 ∧ (knownCover1998_37_4_3_on hv).card = 1998 := by
  exact ⟨relabel_isCover _ knownCover1998_37_4_3_optimal.1,
    (relabel_card _ _).trans knownCover1998_37_4_3_optimal.2⟩

theorem lower_bound_37_4_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 37) (hC : IsCover C 4 3) : 1998 ≤ C.card := by
  classical
  exact QuadrupleAssembly.lower_bound (u := 3) (by decide) hv hC

theorem covering_number_37_4_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 37) :
    (∃ C : Family α, IsCover C 4 3 ∧ C.card = 1998) ∧
    (∀ C : Family α, IsCover C 4 3 → 1998 ≤ C.card) := by
  classical
  exact ⟨⟨knownCover1998_37_4_3_on hv,knownCover1998_37_4_3_on_optimal hv⟩,
    fun _ hC => lower_bound_37_4_3 hv hC⟩

theorem covering_number_37_4_3 :
    (∃ C : Family (Fin 37), IsCover C 4 3 ∧ C.card = 1998) ∧
    (∀ C : Family (Fin 37), IsCover C 4 3 → 1998 ≤ C.card) :=
  covering_number_37_4_3_on (Fintype.card_fin 37)

def knownCover4704_49_4_3 : Family (Fin 49) := WitnessData.V49.blocks

theorem knownCover4704_49_4_3_optimal : IsCover knownCover4704_49_4_3 4 3 ∧ knownCover4704_49_4_3.card = 4704 := WitnessData.V49.optimal

noncomputable def knownCover4704_49_4_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 49) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover4704_49_4_3

theorem knownCover4704_49_4_3_on_optimal {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 49) :
    IsCover (knownCover4704_49_4_3_on hv) 4 3 ∧ (knownCover4704_49_4_3_on hv).card = 4704 := by
  exact ⟨relabel_isCover _ knownCover4704_49_4_3_optimal.1,
    (relabel_card _ _).trans knownCover4704_49_4_3_optimal.2⟩

theorem lower_bound_49_4_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 49) (hC : IsCover C 4 3) : 4704 ≤ C.card := by
  classical
  exact QuadrupleAssembly.lower_bound (u := 4) (by decide) hv hC

theorem covering_number_49_4_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 49) :
    (∃ C : Family α, IsCover C 4 3 ∧ C.card = 4704) ∧
    (∀ C : Family α, IsCover C 4 3 → 4704 ≤ C.card) := by
  classical
  exact ⟨⟨knownCover4704_49_4_3_on hv,knownCover4704_49_4_3_on_optimal hv⟩,
    fun _ hC => lower_bound_49_4_3 hv hC⟩

theorem covering_number_49_4_3 :
    (∃ C : Family (Fin 49), IsCover C 4 3 ∧ C.card = 4704) ∧
    (∀ C : Family (Fin 49), IsCover C 4 3 → 4704 ≤ C.card) :=
  covering_number_49_4_3_on (Fintype.card_fin 49)

def knownCover9150_61_4_3 : Family (Fin 61) := WitnessData.V61.blocks

theorem knownCover9150_61_4_3_optimal : IsCover knownCover9150_61_4_3 4 3 ∧ knownCover9150_61_4_3.card = 9150 := WitnessData.V61.optimal

noncomputable def knownCover9150_61_4_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 61) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover9150_61_4_3

theorem knownCover9150_61_4_3_on_optimal {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 61) :
    IsCover (knownCover9150_61_4_3_on hv) 4 3 ∧ (knownCover9150_61_4_3_on hv).card = 9150 := by
  exact ⟨relabel_isCover _ knownCover9150_61_4_3_optimal.1,
    (relabel_card _ _).trans knownCover9150_61_4_3_optimal.2⟩

theorem lower_bound_61_4_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 61) (hC : IsCover C 4 3) : 9150 ≤ C.card := by
  classical
  exact QuadrupleAssembly.lower_bound (u := 5) (by decide) hv hC

theorem covering_number_61_4_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 61) :
    (∃ C : Family α, IsCover C 4 3 ∧ C.card = 9150) ∧
    (∀ C : Family α, IsCover C 4 3 → 9150 ≤ C.card) := by
  classical
  exact ⟨⟨knownCover9150_61_4_3_on hv,knownCover9150_61_4_3_on_optimal hv⟩,
    fun _ hC => lower_bound_61_4_3 hv hC⟩

theorem covering_number_61_4_3 :
    (∃ C : Family (Fin 61), IsCover C 4 3 ∧ C.card = 9150) ∧
    (∀ C : Family (Fin 61), IsCover C 4 3 → 9150 ≤ C.card) :=
  covering_number_61_4_3_on (Fintype.card_fin 61)

def knownCover15768_73_4_3 : Family (Fin 73) := WitnessData.V73.blocks

theorem knownCover15768_73_4_3_optimal : IsCover knownCover15768_73_4_3 4 3 ∧ knownCover15768_73_4_3.card = 15768 := WitnessData.V73.optimal

noncomputable def knownCover15768_73_4_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 73) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover15768_73_4_3

theorem knownCover15768_73_4_3_on_optimal {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 73) :
    IsCover (knownCover15768_73_4_3_on hv) 4 3 ∧ (knownCover15768_73_4_3_on hv).card = 15768 := by
  exact ⟨relabel_isCover _ knownCover15768_73_4_3_optimal.1,
    (relabel_card _ _).trans knownCover15768_73_4_3_optimal.2⟩

theorem lower_bound_73_4_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 73) (hC : IsCover C 4 3) : 15768 ≤ C.card := by
  classical
  exact QuadrupleAssembly.lower_bound (u := 6) (by decide) hv hC

theorem covering_number_73_4_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 73) :
    (∃ C : Family α, IsCover C 4 3 ∧ C.card = 15768) ∧
    (∀ C : Family α, IsCover C 4 3 → 15768 ≤ C.card) := by
  classical
  exact ⟨⟨knownCover15768_73_4_3_on hv,knownCover15768_73_4_3_on_optimal hv⟩,
    fun _ hC => lower_bound_73_4_3 hv hC⟩

theorem covering_number_73_4_3 :
    (∃ C : Family (Fin 73), IsCover C 4 3 ∧ C.card = 15768) ∧
    (∀ C : Family (Fin 73), IsCover C 4 3 → 15768 ≤ C.card) :=
  covering_number_73_4_3_on (Fintype.card_fin 73)

def knownCover24990_85_4_3 : Family (Fin 85) := WitnessData.V85.blocks

theorem knownCover24990_85_4_3_optimal : IsCover knownCover24990_85_4_3 4 3 ∧ knownCover24990_85_4_3.card = 24990 := WitnessData.V85.optimal

noncomputable def knownCover24990_85_4_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 85) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover24990_85_4_3

theorem knownCover24990_85_4_3_on_optimal {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 85) :
    IsCover (knownCover24990_85_4_3_on hv) 4 3 ∧ (knownCover24990_85_4_3_on hv).card = 24990 := by
  exact ⟨relabel_isCover _ knownCover24990_85_4_3_optimal.1,
    (relabel_card _ _).trans knownCover24990_85_4_3_optimal.2⟩

theorem lower_bound_85_4_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 85) (hC : IsCover C 4 3) : 24990 ≤ C.card := by
  classical
  exact QuadrupleAssembly.lower_bound (u := 7) (by decide) hv hC

theorem covering_number_85_4_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 85) :
    (∃ C : Family α, IsCover C 4 3 ∧ C.card = 24990) ∧
    (∀ C : Family α, IsCover C 4 3 → 24990 ≤ C.card) := by
  classical
  exact ⟨⟨knownCover24990_85_4_3_on hv,knownCover24990_85_4_3_on_optimal hv⟩,
    fun _ hC => lower_bound_85_4_3 hv hC⟩

theorem covering_number_85_4_3 :
    (∃ C : Family (Fin 85), IsCover C 4 3 ∧ C.card = 24990) ∧
    (∀ C : Family (Fin 85), IsCover C 4 3 → 24990 ≤ C.card) :=
  covering_number_85_4_3_on (Fintype.card_fin 85)

def knownCover37248_97_4_3 : Family (Fin 97) := WitnessData.V97.blocks

theorem knownCover37248_97_4_3_optimal : IsCover knownCover37248_97_4_3 4 3 ∧ knownCover37248_97_4_3.card = 37248 := WitnessData.V97.optimal

noncomputable def knownCover37248_97_4_3_on {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 97) : Family α :=
  relabel (Fintype.equivFinOfCardEq hv).symm knownCover37248_97_4_3

theorem knownCover37248_97_4_3_on_optimal {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 97) :
    IsCover (knownCover37248_97_4_3_on hv) 4 3 ∧ (knownCover37248_97_4_3_on hv).card = 37248 := by
  exact ⟨relabel_isCover _ knownCover37248_97_4_3_optimal.1,
    (relabel_card _ _).trans knownCover37248_97_4_3_optimal.2⟩

theorem lower_bound_97_4_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 97) (hC : IsCover C 4 3) : 37248 ≤ C.card := by
  classical
  exact QuadrupleAssembly.lower_bound (u := 8) (by decide) hv hC

theorem covering_number_97_4_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 97) :
    (∃ C : Family α, IsCover C 4 3 ∧ C.card = 37248) ∧
    (∀ C : Family α, IsCover C 4 3 → 37248 ≤ C.card) := by
  classical
  exact ⟨⟨knownCover37248_97_4_3_on hv,knownCover37248_97_4_3_on_optimal hv⟩,
    fun _ hC => lower_bound_97_4_3 hv hC⟩

theorem covering_number_97_4_3 :
    (∃ C : Family (Fin 97), IsCover C 4 3 ∧ C.card = 37248) ∧
    (∀ C : Family (Fin 97), IsCover C 4 3 → 37248 ≤ C.card) :=
  covering_number_97_4_3_on (Fintype.card_fin 97)

end CoveringDesigns
