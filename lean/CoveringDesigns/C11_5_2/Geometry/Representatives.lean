import CoveringDesigns.C11_5_2.Geometry.Basic
import CoveringDesigns.C11_5_2.Representatives
import Mathlib.Tactic.FinCases

/-! Coordinates for the four couples of each of the two fixed witnesses.
All checks below concern these displayed families only. They do not enumerate
coverings and do not prove or assume the Stanton classification. -/

namespace CoveringDesigns.StantonGeometry

open Finset

def representativeShort (tag : Bool) : Finset (Fin 11) :=
  if tag then {0, 4, 8, 9, 10} else {0, 1, 2, 3, 4}

def representativeCouple (tag : Bool) : Fin 4 → Finset (Fin 11) :=
  if tag then ![{0, 4}, {1, 5}, {2, 6}, {3, 7}]
  else ![{3, 9}, {4, 10}, {5, 7}, {6, 8}]

def representativeTriads (tag : Bool) : Fin 4 → Fin 3 → Finset (Fin 11) :=
  if tag then
    ![![{1, 5, 8}, {2, 6, 9}, {3, 7, 10}],
      ![{0, 4, 8}, {3, 7, 9}, {2, 6, 10}],
      ![{3, 7, 8}, {0, 4, 9}, {1, 5, 10}],
      ![{2, 6, 8}, {1, 5, 9}, {0, 4, 10}]]
  else
    ![![{0, 5, 7}, {1, 6, 8}, {2, 4, 10}],
      ![{1, 5, 7}, {0, 6, 8}, {2, 3, 9}],
      ![{2, 6, 8}, {0, 3, 9}, {1, 4, 10}],
      ![{2, 5, 7}, {1, 3, 9}, {0, 4, 10}]]

def representativeSelected (tag : Bool) : Fin 4 → Fin 3 → Fin 11 :=
  if tag then fun _ => ![8, 9, 10]
  else ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]]

section FixedChecks
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem representative_short_mem (tag : Bool) :
    representativeShort tag ∈ stantonRepresentative tag := by
  cases tag <;> decide +kernel

theorem representative_short_iff_mem (tag : Bool) :
    ∀ B ∈ stantonRepresentative tag,
      IsShortBlock (stantonRepresentative tag) B ↔ B = representativeShort tag := by
  cases tag <;> decide +kernel

theorem representative_couples_complete (tag : Bool) :
    ∀ K ∈ (univ : Finset (Fin 11)).powersetCard 2,
      IsCouple (stantonRepresentative tag) K → ∃ i, representativeCouple tag i = K := by
  cases tag <;> decide +kernel

end FixedChecks

theorem representative_short_iff (tag : Bool) (B : Finset (Fin 11)) :
    IsShortBlock (stantonRepresentative tag) B ↔ B = representativeShort tag := by
  constructor
  · intro h
    exact (representative_short_iff_mem tag B h.1).mp h
  · rintro rfl
    exact (representative_short_iff_mem tag _ (representative_short_mem tag)).mpr rfl

def representativeFrame (tag : Bool) (i : Fin 4) :
    MarkingFrame (stantonRepresentative tag) (representativeCouple tag i) where
  triads := representativeTriads tag i
  selected := representativeSelected tag i
  shortBlock := representativeShort tag
  couple_card := by cases tag <;> fin_cases i <;> decide +kernel
  triad_card := by cases tag <;> fin_cases i <;> decide +kernel
  triads_disjoint := by unfold Pairwise; cases tag <;> fin_cases i <;> decide +kernel
  triads_union := by cases tag <;> fin_cases i <;> decide +kernel
  selected_mem := by cases tag <;> fin_cases i <;> decide +kernel
  shortBlock_card := by cases tag <;> decide +kernel
  selected_subset := by cases tag <;> fin_cases i <;> decide +kernel
  short_iff := representative_short_iff tag
  selected_iff := by cases tag <;> fin_cases i <;> decide +kernel
  blocks_eq := by cases tag <;> fin_cases i <;> decide +kernel

theorem representative_marking_frame (tag : Bool) {K : Finset (Fin 11)}
    (hK : IsCouple (stantonRepresentative tag) K) :
    Nonempty (MarkingFrame (stantonRepresentative tag) K) := by
  obtain ⟨i, rfl⟩ := representative_couples_complete tag K
    (mem_powersetCard_univ.mpr hK.1) hK
  exact ⟨representativeFrame tag i⟩

#guard_standard_axioms representativeFrame representative_marking_frame

end CoveringDesigns.StantonGeometry
