import CoveringDesigns.QuadrupleAssembly.Contracts

namespace CoveringDesigns.QuadrupleAssembly
open Finset

def classA {u : ℕ} (H : Family (Core u)) : Family (Point u) :=
  H.image (fun B => B.map (coreEmbedding u))

def classB {u : ℕ} (G : Family (Core u)) : Family (Point u) :=
  G.image (fun B => insert none (B.map (coreEmbedding u)))

def classC {u : ℕ} (L : Family Local) : Family (Point u) :=
  (univ : Finset (Fin u)).biUnion (fun h => L.image (fun B => B.map (holeEmbedding h)))

abbrev HolePair (u : ℕ) := {p : Fin u × Fin u // p.1 < p.2}

abbrev PairIndex (u : ℕ) (F : Fin 5 → Family (Fin 6)) :=
  HolePair u × Fin 2 × Fin 2 × (Σ r : Fin 5, (F r) × (F r))

def pairBlock {u : ℕ} {F : Fin 5 → Family (Fin 6)} (p : PairIndex u F) : Finset (Point u) :=
  (p.2.2.2.2.1.val.map (groupEmbedding (p.1.val.1,p.2.1))) ∪
    (p.2.2.2.2.2.val.map (groupEmbedding (p.1.val.2,p.2.2.1)))

def classD {u : ℕ} (F : Fin 5 → Family (Fin 6)) : Family (Point u) :=
  (univ : Finset (PairIndex u F)).image pairBlock

/-- Four finite images, with their actual points and blocks retained. -/
def assembly {u : ℕ} (H G : Family (Core u)) (L : Family Local)
    (F : Fin 5 → Family (Fin 6)) : Family (Point u) :=
  classA H ∪ classB G ∪ classC L ∪ classD F

private theorem some_not_none {u : ℕ} (B : Finset (Core u)) :
    none ∉ B.map (coreEmbedding u) := by simp [coreEmbedding]

theorem classA_uniform {u : ℕ} {H : Family (Core u)} (hH : HSeed H) :
    Uniform (classA H) 4 := by
  intro B hB
  obtain ⟨D,hD,rfl⟩ := mem_image.mp hB
  simpa using hH.uniform D hD

theorem classB_uniform {u : ℕ} {G : Family (Core u)} (hG : GDDSeed G) :
    Uniform (classB G) 4 := by
  intro B hB
  obtain ⟨D,hD,rfl⟩ := mem_image.mp hB
  rw [card_insert_of_notMem (some_not_none D), card_map, hG.uniform D hD]

theorem classC_uniform {u : ℕ} {L : Family Local} (hL : IsCover L 4 3) :
    Uniform (classC (u := u) L) 4 := by
  intro B hB
  obtain ⟨h,_,hB⟩ := mem_biUnion.mp hB
  obtain ⟨D,hD,rfl⟩ := mem_image.mp hB
  simpa using hL.1 D hD

private theorem different_groups {u : ℕ} (g h : Group u) (hne : g ≠ h)
    (E D : Finset (Fin 6)) :
    Disjoint (E.map (groupEmbedding g)) (D.map (groupEmbedding h)) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,_,rfl⟩ := mem_map.mp hx
  obtain ⟨b,_,he⟩ := mem_map.mp hy
  apply hne
  change some (h,b) = some (g,a) at he
  exact congrArg Prod.fst (Option.some.inj he).symm

theorem pairBlock_card {u : ℕ} {F : Fin 5 → Family (Fin 6)}
    (hF : Factors F) (p : PairIndex u F) : (pairBlock p).card = 4 := by
  rw [pairBlock, card_union_of_disjoint]
  · simp only [card_map]
    rw [hF.uniform _ _ p.2.2.2.2.1.property, hF.uniform _ _ p.2.2.2.2.2.property]
  · apply different_groups
    intro he
    have hsame := congrArg Prod.fst he
    exact (ne_of_lt p.1.property) hsame

theorem classD_uniform {u : ℕ} {F : Fin 5 → Family (Fin 6)} (hF : Factors F) :
    Uniform (classD (u := u) F) 4 := by
  intro B hB
  obtain ⟨p,_,rfl⟩ := mem_image.mp hB
  exact pairBlock_card hF p

theorem assembly_uniform {u : ℕ} {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hH : HSeed H) (hG : GDDSeed G)
    (hL : IsCover L 4 3) (hF : Factors F) : Uniform (assembly H G L F) 4 := by
  intro B hB
  rcases mem_union.mp hB with hB | hB
  · rcases mem_union.mp hB with hB | hB
    · rcases mem_union.mp hB with hB | hB
      · exact classA_uniform hH B hB
      · exact classB_uniform hG B hB
    · exact classC_uniform hL B hB
  · exact classD_uniform hF B hB

end CoveringDesigns.QuadrupleAssembly
