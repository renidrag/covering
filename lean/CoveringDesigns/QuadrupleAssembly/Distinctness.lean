import CoveringDesigns.QuadrupleAssembly.Budget

namespace CoveringDesigns.QuadrupleAssembly
open Finset

def fillingBlock {u : ℕ} {L : Family Local} (p : Fin u × L) : Finset (Point u) :=
  p.2.val.map (holeEmbedding p.1)

private theorem classC_indexed {u : ℕ} (L : Family Local) :
    classC (u := u) L = (univ : Finset (Fin u × L)).image fillingBlock := by
  ext D
  simp [classC,fillingBlock]

/-- All four sources are injective on their actual index domains. In particular
no silent removal of repeated occurrences is part of the cardinality proof. -/
theorem sources_injective {u : ℕ} (hu : 3 ≤ u) {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hH : HSeed H) (hG : GDDSeed G)
    (hL : IsCover L 4 3) (hLc : L.card = 78) (hF : Factors F) :
    Set.InjOn (fun B => B.map (coreEmbedding u)) (H : Set (Finset (Core u))) ∧
    Set.InjOn (fun B => insert none (B.map (coreEmbedding u))) (G : Set (Finset (Core u))) ∧
    Function.Injective (fillingBlock (u := u) (L := L)) ∧
    Function.Injective (pairBlock (u := u) (F := F)) := by
  obtain ⟨_,ha,hb,hc,hd,_⟩ := assembly_sharp hu hH hG hL hLc hF
  refine ⟨card_image_iff.mp ?_,card_image_iff.mp ?_,?_,?_⟩
  · exact ha.trans (h_seed_card hH).symm
  · exact hb.trans (gdd_seed_card hG).symm
  · rw [classC_indexed] at hc
    have he : ((univ : Finset (Fin u × L)).image fillingBlock).card =
        (univ : Finset (Fin u × L)).card := by
      rw [hc]
      simp [hLc,Nat.mul_comm]
    have hi := card_image_iff.mp he
    intro x y hxy
    exact hi (mem_univ _) (mem_univ _) hxy
  · have he : ((univ : Finset (PairIndex u F)).image pairBlock).card =
        (univ : Finset (PairIndex u F)).card := by
      rw [← classD,hd,card_univ,pair_index_card hF]
    have hi := card_image_iff.mp he
    intro x y hxy
    exact hi (mem_univ _) (mem_univ _) hxy

/-- The six pairwise separations of the four actual block classes. -/
theorem classes_disjoint {u : ℕ} (hu : 3 ≤ u) {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hH : HSeed H) (hG : GDDSeed G)
    (hL : IsCover L 4 3) (hLc : L.card = 78) (hF : Factors F) :
    Disjoint (classA H) (classB G) ∧ Disjoint (classA H) (classC L) ∧
    Disjoint (classA H) (classD F) ∧ Disjoint (classB G) (classC L) ∧
    Disjoint (classB G) (classD F) ∧ Disjoint (classC (u := u) L) (classD F) := by
  obtain ⟨_,_,_,_,_,hab,habc,habcd⟩ := assembly_sharp hu hH hG hL hLc hF
  simp only [disjoint_union_left] at habc habcd
  exact ⟨hab,habc.1,habcd.1.1,habc.2,habcd.1.2,habcd.2⟩

end CoveringDesigns.QuadrupleAssembly
