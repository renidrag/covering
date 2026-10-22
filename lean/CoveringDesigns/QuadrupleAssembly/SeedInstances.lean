import CoveringDesigns.QuadrupleAssembly.Rows
import CoveringDesigns.QuadrupleAssembly.SeedData.H4Six
import CoveringDesigns.QuadrupleAssembly.SeedData.H4Two
import CoveringDesigns.QuadrupleAssembly.SeedData.Hanani
import CoveringDesigns.QuadrupleAssembly.SeedData.LatinSix
import CoveringDesigns.QuadrupleAssembly.SeedData.Master8
import CoveringDesigns.QuadrupleAssembly.SeedData.Master10
import CoveringDesigns.QuadrupleAssembly.SeedData.Master12
import CoveringDesigns.QuadrupleAssembly.SeedData.Master14
import CoveringDesigns.QuadrupleAssembly.SeedData.Master16
import CoveringDesigns.QuadrupleAssembly.SeedData.GDD2_4
import CoveringDesigns.QuadrupleAssembly.SeedData.GDD2_6
import CoveringDesigns.QuadrupleAssembly.SeedData.GDD2_7
import CoveringDesigns.QuadrupleAssembly.SeedData.GDD4_4
import CoveringDesigns.QuadrupleAssembly.SeedData.FourGDD3_5
import CoveringDesigns.QuadrupleAssembly.SeedData.FourGDD3_8
import CoveringDesigns.QuadrupleAssembly.SeedData.PilotGDD
import CoveringDesigns.QuadrupleAssembly.SeedData.Filling
import Mathlib.Tactic.IntervalCases

namespace CoveringDesigns.QuadrupleAssembly
open Finset SeedData

def productRows {m w : ℕ} (rows : List (Finset (Fin (m*w)))) :=
  transportRows finProdFinEquiv.symm rows

theorem productRows_valid {m w k t : ℕ} {rows : List (Finset (Fin (m*w)))}
    (h : GroupDesign (fun x => x.val / w) k t rows.toFinset) :
    GroupDesign Prod.fst k t (productRows rows).toFinset := by
  rw [productRows,transportRows_family]
  exact productFamily_valid h

def binaryRows : (n : ℕ) → List (Finset (Fin n × Fin 2))
  | 4 => productRows H4Two.rows
  | _ => []

def h6RawRows := substitutionRows Hanani.rows binaryRows

theorem h6Raw_valid : GroupDesign (fun p : Fin 18 × Fin 2 => p.1.val / 3)
    4 3 h6RawRows.toFinset := by
  rw [h6RawRows,substitutionRows_family]
  apply productSubstitute_valid _ Hanani.valid.master
  intro B hB
  have hc := Hanani.valid.uniform B hB
  rw [hc]
  exact productRows_valid H4Two.valid

def h6Equiv : (Fin 18 × Fin 2) ≃ (Fin 6 × Fin 6) :=
  (finProdFinEquiv.trans (finCongr (show 18*2 = 6*6 by decide))).trans finProdFinEquiv.symm

def h6Rows := transportRows h6Equiv h6RawRows

theorem h6_valid : GroupDesign Prod.fst 4 3 h6Rows.toFinset := by
  rw [h6Rows,transportRows_family]
  apply GroupDesign.of_injective_groups (fun i : Fin 6 => i.val) Fin.val_injective
  apply h6Raw_valid.relabel h6Equiv
  intro p
  change (p.2.val+2*p.1.val)/6 = p.1.val/3
  have := p.2.isLt
  omega

def hTemplateRows : (n : ℕ) → List (Finset (Fin n × Fin 6))
  | 4 => productRows H4Six.rows
  | 6 => h6Rows
  | _ => []

theorem hTemplate_valid {n : ℕ} (h : n = 4 ∨ n = 6) :
    GroupDesign Prod.fst 4 3 (hTemplateRows n).toFinset := by
  rcases h with rfl | rfl
  · exact productRows_valid H4Six.valid
  · exact h6_valid

def groupEquiv (u : ℕ) : Group u ≃ Fin (2*u) :=
  finProdFinEquiv.trans (finCongr (by omega))

def groupedEquiv (u : ℕ) : (Fin (2*u) × Fin 6) ≃ Core u :=
  Equiv.prodCongr (groupEquiv u).symm (Equiv.refl _)

def hFromRows {u : ℕ} (rows : List (Finset (Fin (2*u)))) :=
  transportRows (groupedEquiv u) (substitutionRows rows hTemplateRows)

theorem hFrom_valid {u : ℕ} {rows : List (Finset (Fin (2*u)))}
    (h : Master id 3 rows.toFinset)
    (hs : ∀ B ∈ rows.toFinset, B.card = 4 ∨ B.card = 6) : HSeed (hFromRows rows).toFinset := by
  rw [hFromRows,transportRows_family]
  have ht : GroupDesign Prod.fst 4 3 (substitutionRows rows hTemplateRows).toFinset := by
    rw [substitutionRows_family]
    exact productSubstitute_valid id h _ (fun B hB => hTemplate_valid (hs B hB))
  apply GroupDesign.of_injective_groups (groupEquiv u) (groupEquiv u).injective
  exact ht.relabel (groupedEquiv u) (fun p => by simp [groupedEquiv])

def latinRows : (n : ℕ) → List (Finset (Fin n × Fin 6))
  | 3 => productRows LatinSix.rows
  | _ => []

def gLatinRows {u : ℕ} (rows : List (Finset (Fin (2*u)))) :=
  transportRows (groupedEquiv u) (substitutionRows rows latinRows)

theorem gLatin_valid {u : ℕ} {rows : List (Finset (Fin (2*u)))}
    (h : GroupDesign (fun x => x.val / 2) 3 2 rows.toFinset) :
    GDDSeed (gLatinRows rows).toFinset := by
  rw [gLatinRows,transportRows_family]
  have ht : GroupDesign (fun p : Fin (2*u) × Fin 6 => p.1.val / 2)
      3 2 (substitutionRows rows latinRows).toFinset := by
    rw [substitutionRows_family]
    apply productSubstitute_valid _ h.master
    intro B hB
    rw [h.uniform B hB]
    exact productRows_valid LatinSix.valid
  apply GroupDesign.of_injective_groups (fun i : Fin u => i.val) Fin.val_injective
  exact ht.relabel (groupedEquiv u) (fun _ => rfl)

def fourRows : (n : ℕ) → List (Finset (Fin n × Fin 4))
  | 4 => productRows GDD4_4.rows
  | _ => []

def fourEquiv (u : ℕ) : (Fin (3*u) × Fin 4) ≃ Core u :=
  (finProdFinEquiv.trans (finCongr (by omega))).trans (coreEquiv u).symm

theorem core_hole_val {u : ℕ} (x : Fin (12*u)) :
    (hole ((coreEquiv u).symm x)).val = x.val / 12 := by
  change x.val / 6 / 2 = x.val / 12
  omega

def gFourRows {u : ℕ} (rows : List (Finset (Fin (3*u)))) :=
  transportRows (fourEquiv u) (substitutionRows rows fourRows)

theorem gFour_valid {u : ℕ} {rows : List (Finset (Fin (3*u)))}
    (h : GroupDesign (fun x => x.val / 3) 4 2 rows.toFinset) :
    GDDSeed (gFourRows rows).toFinset := by
  rw [gFourRows,transportRows_family]
  have ht : GroupDesign (fun p : Fin (3*u) × Fin 4 => p.1.val / 3)
      3 2 (substitutionRows rows fourRows).toFinset := by
    rw [substitutionRows_family]
    apply productSubstitute_valid _ h.master
    intro B hB
    rw [h.uniform B hB]
    exact productRows_valid GDD4_4.valid
  apply GroupDesign.of_injective_groups (fun i : Fin u => i.val) Fin.val_injective
  apply ht.relabel (fourEquiv u)
  intro p
  change (hole ((coreEquiv u).symm _)).val = _
  rw [core_hole_val]
  change (p.2.val+4*p.1.val)/12 = p.1.val/3
  have := p.2.isLt
  omega

def hRows : (u : ℕ) → List (Finset (Core u))
  | 3 => transportRows (groupedEquiv 3) h6Rows
  | 4 => hFromRows Master8.rows
  | 5 => hFromRows Master10.rows
  | 6 => hFromRows Master12.rows
  | 7 => hFromRows Master14.rows
  | 8 => hFromRows Master16.rows
  | _ => []

def gRows : (u : ℕ) → List (Finset (Core u))
  | 3 => transportRows (coreEquiv 3).symm PilotGDD.rows
  | 4 => gLatinRows GDD2_4.rows
  | 5 => gFourRows FourGDD3_5.rows
  | 6 => gLatinRows GDD2_6.rows
  | 7 => gLatinRows GDD2_7.rows
  | 8 => gFourRows FourGDD3_8.rows
  | _ => []

theorem h_valid {u : ℕ} (hlo : 3 ≤ u) (hhi : u ≤ 8) : HSeed (hRows u).toFinset := by
  interval_cases u
  · change HSeed (transportRows (groupedEquiv 3) h6Rows).toFinset
    rw [transportRows_family]
    apply GroupDesign.of_injective_groups (groupEquiv 3) (groupEquiv 3).injective
    exact h6_valid.relabel (groupedEquiv 3) (fun p => by simp [groupedEquiv])
  · exact hFrom_valid Master8.valid.master (fun B hB => Or.inl (Master8.valid.uniform B hB))
  · exact hFrom_valid Master10.valid.master (fun B hB => Or.inl (Master10.valid.uniform B hB))
  · exact hFrom_valid Master12.valid Master12.sizes
  · exact hFrom_valid Master14.valid.master (fun B hB => Or.inl (Master14.valid.uniform B hB))
  · exact hFrom_valid Master16.valid.master (fun B hB => Or.inl (Master16.valid.uniform B hB))

theorem g_valid {u : ℕ} (hlo : 3 ≤ u) (hhi : u ≤ 8) : GDDSeed (gRows u).toFinset := by
  interval_cases u
  · change GDDSeed (transportRows (coreEquiv 3).symm PilotGDD.rows).toFinset
    rw [transportRows_family]
    apply GroupDesign.of_injective_groups (fun i : Fin 3 => i.val) Fin.val_injective
    exact PilotGDD.valid.relabel (coreEquiv 3).symm (fun x => core_hole_val (u := 3) x)
  · exact gLatin_valid GDD2_4.valid
  · exact gFour_valid FourGDD3_5.valid
  · exact gLatin_valid GDD2_6.valid
  · exact gLatin_valid GDD2_7.valid
  · exact gFour_valid FourGDD3_8.valid

def fillingRows := transportRows localEquiv.symm Filling.rows
def filling := fillingRows.toFinset

theorem filling_valid : IsCover filling 4 3 := by
  rw [filling,fillingRows,transportRows_family]
  exact relabel_isCover localEquiv.symm Filling.valid

theorem filling_card : filling.card = 78 := by
  rw [filling,fillingRows,transportRows_family,relabel_card]
  exact Filling.size

def factorRows (r : Fin 5) : List (Finset (Fin 6)) :=
  match r.val with
  | 0 => [{5,0},{1,4},{2,3}]
  | 1 => [{5,1},{2,0},{3,4}]
  | 2 => [{5,2},{3,1},{4,0}]
  | 3 => [{5,3},{4,2},{0,1}]
  | _ => [{5,4},{0,3},{1,2}]

def factors (r : Fin 5) := (factorRows r).toFinset

theorem factors_valid : Factors factors := by
  refine ⟨?_,?_,?_⟩ <;> simp only [Uniform,ExistsUnique] <;> decide +kernel

end CoveringDesigns.QuadrupleAssembly
