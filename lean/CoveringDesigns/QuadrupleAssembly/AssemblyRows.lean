import CoveringDesigns.QuadrupleAssembly.SeedInstances
import CoveringDesigns.QuadrupleAssembly.Distinctness

namespace CoveringDesigns.QuadrupleAssembly
open Finset

def aRows (u : ℕ) := (hRows u).map (fun B => B.map (coreEmbedding u))
def bRows (u : ℕ) := (gRows u).map (fun B => insert none (B.map (coreEmbedding u)))
def cRows (u : ℕ) := (List.finRange u).flatMap
  (fun h => fillingRows.map (fun B => B.map (holeEmbedding h)))

def dPiece {u : ℕ} (h k : Fin u) (b c : Fin 2) :=
  (List.finRange 5).flatMap (fun r => (factorRows r).flatMap (fun E =>
    (factorRows r).map (fun D => E.map (groupEmbedding (h,b)) ∪ D.map (groupEmbedding (k,c)))))

def dRows (u : ℕ) := (List.finRange u).flatMap (fun h =>
  (List.finRange u).flatMap (fun k => if h < k then
    (List.finRange 2).flatMap (fun b => (List.finRange 2).flatMap (dPiece h k b)) else []))

theorem dRows_family (u : ℕ) : (dRows u).toFinset = classD (u := u) factors := by
  ext B
  simp only [List.mem_toFinset, dRows, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨h,k,hB⟩
    split_ifs at hB with hk
    · simp only [List.mem_flatMap,List.mem_finRange,true_and] at hB
      obtain ⟨b,c,hB⟩ := hB
      simp only [dPiece,List.mem_flatMap,List.mem_finRange,true_and,List.mem_map] at hB
      obtain ⟨r,E,hE,D,hD,rfl⟩ := hB
      exact mem_image.mpr ⟨(⟨(h,k),hk⟩,b,c,⟨r,⟨E,by simpa [factors] using hE⟩,
        ⟨D,by simpa [factors] using hD⟩⟩),mem_univ _,rfl⟩
    · simp at hB
  · rintro hB
    obtain ⟨p,_,rfl⟩ := mem_image.mp hB
    refine ⟨p.1.val.1,p.1.val.2,?_⟩
    rw [ite_eq_left_iff.mpr (fun hn => False.elim (hn p.1.property))]
    simp only [List.mem_flatMap,List.mem_finRange,true_and]
    refine ⟨p.2.1,p.2.2.1,?_⟩
    simp only [dPiece,List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
    refine ⟨p.2.2.2.1,p.2.2.2.2.1.val,?_,p.2.2.2.2.2.val,?_,rfl⟩
    · exact List.mem_toFinset.mp p.2.2.2.2.1.property
    · exact List.mem_toFinset.mp p.2.2.2.2.2.property

def assemblyRows (u : ℕ) := aRows u ++ bRows u ++ cRows u ++ dRows u

theorem assemblyRows_family (u : ℕ) : (assemblyRows u).toFinset =
    assembly (hRows u).toFinset (gRows u).toFinset filling factors := by
  have ha : (aRows u).toFinset = classA (hRows u).toFinset := by ext; simp [aRows,classA]
  have hb : (bRows u).toFinset = classB (gRows u).toFinset := by ext; simp [bRows,classB]
  have hc : (cRows u).toFinset = classC (u := u) filling := by
    ext; simp [cRows,classC,filling]
  simp only [assemblyRows,List.toFinset_append,ha,hb,hc,dRows_family,assembly]

def labelledRows (u : ℕ) := transportRows (labelEquiv u) (assemblyRows u)
def labelledFamily (u : ℕ) := (labelledRows u).toFinset

theorem labelledFamily_optimal {u : ℕ} (hlo : 3 ≤ u) (hhi : u ≤ 8) :
    IsCover (labelledFamily u) 4 3 ∧ (labelledFamily u).card = 6*u^2*(12*u+1) := by
  have h := assembly_optimal hlo (h_valid hlo hhi) (g_valid hlo hhi)
    filling_valid filling_card factors_valid
  rw [labelledFamily,labelledRows,transportRows_family,assemblyRows_family]
  exact ⟨relabel_isCover _ h.1,by simpa only [relabel_card] using h.2⟩

/-- Small row pieces for a transparent lossless distributed-data projection. -/
def hPiece {u : ℕ} (B : Finset (Fin (2*u))) :=
  (hTemplateRows B.card).map (fun D =>
    (((D.map (fastBlockLift B)).map (groupedEquiv u).toEmbedding).map
      (coreEmbedding u)).map (labelEquiv u).toEmbedding)

def hPilotPiece (B : Finset (Fin 18)) :=
  (binaryRows B.card).map (fun D =>
    (((((D.map (fastBlockLift B)).map h6Equiv.toEmbedding).map
      (groupedEquiv 3).toEmbedding).map (coreEmbedding 3)).map (labelEquiv 3).toEmbedding))

def gLatinPiece {u : ℕ} (B : Finset (Fin (2*u))) :=
  (latinRows B.card).map (fun D =>
    (insert none (((D.map (fastBlockLift B)).map (groupedEquiv u).toEmbedding).map
      (coreEmbedding u))).map (labelEquiv u).toEmbedding)

def gFourPiece {u : ℕ} (B : Finset (Fin (3*u))) :=
  (fourRows B.card).map (fun D =>
    (insert none (((D.map (fastBlockLift B)).map (fourEquiv u).toEmbedding).map
      (coreEmbedding u))).map (labelEquiv u).toEmbedding)

def gPilotPiece (B : Finset (Fin 36)) :=
  (insert none ((B.map (coreEquiv 3).symm.toEmbedding).map (coreEmbedding 3))).map
    (labelEquiv 3).toEmbedding

def cPiece {u : ℕ} (h : Fin u) := fillingRows.map (fun B =>
  (B.map (holeEmbedding h)).map (labelEquiv u).toEmbedding)

def labelledDPiece {u : ℕ} (h k : Fin u) (b c : Fin 2) :=
  transportRows (labelEquiv u) (dPiece h k b c)

theorem labelled_hFrom {u : ℕ} (rows : List (Finset (Fin (2*u)))) :
    transportRows (labelEquiv u) ((hFromRows rows).map (fun B => B.map (coreEmbedding u))) =
      rows.flatMap hPiece := by
  simp only [hFromRows,substitutionRows,transportRows,List.map_flatMap,List.map_map]
  rfl

theorem labelled_hPilot : transportRows (labelEquiv 3) (aRows 3) =
    SeedData.Hanani.rows.flatMap hPilotPiece := by
  simp only [aRows,hRows,h6Rows,h6RawRows,substitutionRows,transportRows,
    List.map_flatMap,List.map_map]
  rfl

theorem labelled_gLatin {u : ℕ} (rows : List (Finset (Fin (2*u)))) :
    transportRows (labelEquiv u) ((gLatinRows rows).map (fun B => insert none (B.map (coreEmbedding u)))) =
      rows.flatMap gLatinPiece := by
  simp only [gLatinRows,substitutionRows,transportRows,List.map_flatMap,List.map_map]
  rfl

theorem labelled_gFour {u : ℕ} (rows : List (Finset (Fin (3*u)))) :
    transportRows (labelEquiv u) ((gFourRows rows).map (fun B => insert none (B.map (coreEmbedding u)))) =
      rows.flatMap gFourPiece := by
  simp only [gFourRows,substitutionRows,transportRows,List.map_flatMap,List.map_map]
  rfl

theorem labelled_gPilot : transportRows (labelEquiv 3) (bRows 3) =
    SeedData.PilotGDD.rows.map gPilotPiece := by
  simp only [bRows,gRows,transportRows,List.map_map]
  rfl

theorem labelled_cRows (u : ℕ) : transportRows (labelEquiv u) (cRows u) =
    (List.finRange u).flatMap cPiece := by
  simp only [cRows,transportRows,List.map_flatMap,List.map_map]
  rfl

theorem labelled_dRows (u : ℕ) : transportRows (labelEquiv u) (dRows u) =
    (List.finRange u).flatMap (fun h => (List.finRange u).flatMap (fun k => if h < k then
      (List.finRange 2).flatMap (fun b => (List.finRange 2).flatMap (labelledDPiece h k b)) else [])) := by
  simp only [dRows,transportRows,List.map_flatMap]
  congr 1
  funext h
  congr 1
  funext k
  split_ifs <;> simp only [List.map_flatMap,List.map_nil] <;> rfl

theorem labelledRows_parts (u : ℕ) : labelledRows u =
    transportRows (labelEquiv u) (aRows u) ++ transportRows (labelEquiv u) (bRows u) ++
    transportRows (labelEquiv u) (cRows u) ++ transportRows (labelEquiv u) (dRows u) := by
  simp only [labelledRows,assemblyRows,transportRows,List.map_append]

def dIndices (u : ℕ) : List (Fin u × Fin u × Fin 2 × Fin 2) :=
  (List.finRange u).flatMap (fun h => (List.finRange u).flatMap (fun k => if h < k then
    (List.finRange 2).flatMap (fun b => (List.finRange 2).map (fun c => (h,k,b,c))) else []))

theorem labelled_dIndices (u : ℕ) : transportRows (labelEquiv u) (dRows u) =
    (dIndices u).flatMap (fun p => labelledDPiece p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  rw [labelled_dRows]
  simp only [dIndices,List.flatMap_assoc]
  congr 1
  funext h
  congr 1
  funext k
  split_ifs <;> simp only [List.flatMap_assoc,List.flatMap_map,List.flatMap_nil]

end CoveringDesigns.QuadrupleAssembly
