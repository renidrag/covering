import CoveringDesigns.QuadrupleAssembly.Construction
import Aesop

namespace CoveringDesigns.QuadrupleAssembly
open Finset

private theorem three_subset {α : Type*} [DecidableEq α] (x y z : α) :
    ({x,y,z} : Finset α).card ≤ 3 := by
  have h := card_insert_le x ({y,z} : Finset α)
  have h' := card_insert_le y ({z} : Finset α)
  simp only [card_singleton] at h'
  omega

private theorem local_cover {L : Family Local} (hL : IsCover L 4 3) (a b c : Local) :
    ∃ B ∈ L, ({a,b,c} : Finset Local) ⊆ B := by
  obtain ⟨T,hs,_,ht⟩ := exists_subsuperset_card_eq (subset_univ ({a,b,c} : Finset Local))
    (three_subset a b c) (by simp [Local])
  obtain ⟨B,hB,hTB⟩ := hL.2 T ht
  exact ⟨B,hB,hs.trans hTB⟩

private theorem hole_cover {u : ℕ} {L : Family Local} (hL : IsCover L 4 3)
    (h : Fin u) (a b c : Local) :
    ∃ B ∈ classC (u := u) L,
      ({holeEmbedding h a,holeEmbedding h b,holeEmbedding h c} : Finset (Point u)) ⊆ B := by
  obtain ⟨D,hD,hs⟩ := local_cover hL a b c
  refine ⟨D.map (holeEmbedding h), mem_biUnion.mpr ⟨h,mem_univ _,mem_image.mpr ⟨D,hD,rfl⟩⟩, ?_⟩
  simp only [insert_subset_iff, singleton_subset_iff]
  exact ⟨mem_map.mpr ⟨a,hs (by simp),rfl⟩,
    mem_map.mpr ⟨b,hs (by simp),rfl⟩,mem_map.mpr ⟨c,hs (by simp),rfl⟩⟩

private theorem transverse_three {α G : Type*} [DecidableEq α] (g : α → G)
    {a b c : α} (hab : g a ≠ g b) (hac : g a ≠ g c) (hbc : g b ≠ g c) :
    Transverse g ({a,b,c} : Finset α) := by
  intro x hx y hy he
  simp only [Finset.mem_coe, mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> aesop

private theorem h_cover {u : ℕ} {H : Family (Core u)} (hH : HSeed H)
    (a b c : Core u) (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1) :
    ∃ B ∈ classA H, ({some a,some b,some c} : Finset (Point u)) ⊆ B := by
  have ab : a ≠ b := fun h => hab (congrArg Prod.fst h)
  have ac : a ≠ c := fun h => hac (congrArg Prod.fst h)
  have bc : b ≠ c := fun h => hbc (congrArg Prod.fst h)
  obtain ⟨D,⟨hD,hs⟩,_⟩ := hH.exact {a,b,c} (by simp [ab,ac,bc])
    (transverse_three Prod.fst hab hac hbc)
  refine ⟨D.map (coreEmbedding u), mem_image.mpr ⟨D,hD,rfl⟩, ?_⟩
  simp only [insert_subset_iff, singleton_subset_iff]
  exact ⟨mem_map.mpr ⟨a,hs (by simp),rfl⟩,
    mem_map.mpr ⟨b,hs (by simp),rfl⟩,mem_map.mpr ⟨c,hs (by simp),rfl⟩⟩

private theorem gdd_cover {u : ℕ} {G : Family (Core u)} (hG : GDDSeed G)
    (a b : Core u) (hab : hole a ≠ hole b) :
    ∃ B ∈ classB G, ({none,some a,some b} : Finset (Point u)) ⊆ B := by
  have ab : a ≠ b := fun h => hab (congrArg hole h)
  have ht : Transverse hole ({a,b} : Finset (Core u)) := by
    intro x hx y hy he
    simp only [Finset.mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> aesop
  obtain ⟨D,⟨hD,hs⟩,_⟩ := hG.exact {a,b} (by simp [ab]) ht
  refine ⟨insert none (D.map (coreEmbedding u)), mem_image.mpr ⟨D,hD,rfl⟩, ?_⟩
  simp only [insert_subset_iff, singleton_subset_iff]
  exact ⟨mem_insert_self _ _, mem_insert_of_mem (mem_map.mpr ⟨a,hs (by simp),rfl⟩),
    mem_insert_of_mem (mem_map.mpr ⟨b,hs (by simp),rfl⟩)⟩

private theorem edges_mem {u : ℕ} {F : Fin 5 → Family (Fin 6)}
    (g h : Group u) (hne : g.1 ≠ h.1) (r : Fin 5)
    (E D : Finset (Fin 6)) (hE : E ∈ F r) (hD : D ∈ F r) :
    E.map (groupEmbedding g) ∪ D.map (groupEmbedding h) ∈ classD F := by
  rcases lt_or_gt_of_ne hne with hg | hh
  · let p : PairIndex u F := (⟨(g.1,h.1),hg⟩,g.2,h.2,⟨r,⟨E,hE⟩,⟨D,hD⟩⟩)
    exact mem_image.mpr ⟨p,mem_univ _,rfl⟩
  · let p : PairIndex u F := (⟨(h.1,g.1),hh⟩,h.2,g.2,⟨r,⟨D,hD⟩,⟨E,hE⟩⟩)
    exact mem_image.mpr ⟨p,mem_univ _,by simp [pairBlock,p,union_comm]⟩

private theorem pair_cover {u : ℕ} {F : Fin 5 → Family (Fin 6)} (hF : Factors F)
    (g h : Group u) (hne : g.1 ≠ h.1) (x y z : Fin 6) (hxy : x ≠ y) :
    ∃ B ∈ classD F, ({some (g,x),some (g,y),some (h,z)} : Finset (Point u)) ⊆ B := by
  obtain ⟨r,hr,_⟩ := hF.pairs {x,y} (by simp [hxy])
  obtain ⟨D,⟨hD,hz⟩,_⟩ := hF.partition r z
  refine ⟨({x,y} : Finset (Fin 6)).map (groupEmbedding g) ∪ D.map (groupEmbedding h),
    edges_mem g h hne r {x,y} D hr hD, ?_⟩
  simp only [insert_subset_iff, singleton_subset_iff]
  exact ⟨mem_union_left _ (mem_map.mpr ⟨x,by simp,rfl⟩),
    mem_union_left _ (mem_map.mpr ⟨y,by simp,rfl⟩),
    mem_union_right _ (mem_map.mpr ⟨z,hz,rfl⟩)⟩

private theorem class_subset {u : ℕ} (H G : Family (Core u)) (L : Family Local)
    (F : Fin 5 → Family (Fin 6)) :
    classA H ⊆ assembly H G L F ∧ classB G ⊆ assembly H G L F ∧
    classC L ⊆ assembly H G L F ∧ classD F ⊆ assembly H G L F := by
  unfold assembly
  exact ⟨(subset_union_left.trans subset_union_left).trans subset_union_left,
    (subset_union_right.trans subset_union_left).trans subset_union_left,
    subset_union_right.trans subset_union_left,subset_union_right⟩

private theorem infinity_cover {u : ℕ} {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hG : GDDSeed G) (hL : IsCover L 4 3) (a b : Core u) :
    ∃ B ∈ assembly H G L F, ({none,some a,some b} : Finset (Point u)) ⊆ B := by
  by_cases hh : hole a = hole b
  · obtain ⟨B,hB,hs⟩ := hole_cover hL (hole a) none (some (a.1.2,a.2)) (some (b.1.2,b.2))
    refine ⟨B,(class_subset H G L F).2.2.1 hB, ?_⟩
    have hb : ((hole a,b.1.2),b.2) = b := Prod.ext (Prod.ext hh rfl) rfl
    change ({none,some a,some ((hole a,b.1.2),b.2)} : Finset (Point u)) ⊆ B at hs
    simpa only [hb] using hs
  · obtain ⟨B,hB,hs⟩ := gdd_cover hG a b hh
    exact ⟨B,(class_subset H G L F).2.1 hB,hs⟩

private theorem core_cover {u : ℕ} {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hH : HSeed H) (hL : IsCover L 4 3) (hF : Factors F)
    (a b c : Core u) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ∃ B ∈ assembly H G L F, ({some a,some b,some c} : Finset (Point u)) ⊆ B := by
  by_cases same : hole a = hole b ∧ hole a = hole c
  · obtain ⟨B,hB,hs⟩ := hole_cover hL (hole a)
      (some (a.1.2,a.2)) (some (b.1.2,b.2)) (some (c.1.2,c.2))
    refine ⟨B,(class_subset H G L F).2.2.1 hB, ?_⟩
    have hb : ((hole a,b.1.2),b.2) = b := Prod.ext (Prod.ext same.1 rfl) rfl
    have hc : ((hole a,c.1.2),c.2) = c := Prod.ext (Prod.ext same.2 rfl) rfl
    change ({some a,some ((hole a,b.1.2),b.2),some ((hole a,c.1.2),c.2)} : Finset (Point u)) ⊆ B at hs
    simpa only [hb,hc] using hs
  by_cases gab : a.1 = b.1
  · have hh : a.1.1 ≠ c.1.1 := by
      intro hh; exact same ⟨congrArg Prod.fst gab,hh⟩
    have hxy : a.2 ≠ b.2 := fun he => ab (Prod.ext gab he)
    obtain ⟨B,hB,hs⟩ := pair_cover hF a.1 c.1 hh a.2 b.2 c.2 hxy
    have hb : (a.1,b.2) = b := Prod.ext gab rfl
    exact ⟨B,(class_subset H G L F).2.2.2 hB,by simpa only [hb] using hs⟩
  by_cases gac : a.1 = c.1
  · have hh : a.1.1 ≠ b.1.1 := by
      intro hh; exact same ⟨hh,congrArg Prod.fst gac⟩
    have hxy : a.2 ≠ c.2 := fun he => ac (Prod.ext gac he)
    obtain ⟨B,hB,hs⟩ := pair_cover hF a.1 b.1 hh a.2 c.2 b.2 hxy
    have hc : (a.1,c.2) = c := Prod.ext gac rfl
    refine ⟨B,(class_subset H G L F).2.2.2 hB,?_⟩
    simpa only [hc,Prod.eta,insert_subset_iff,singleton_subset_iff,and_comm,and_left_comm,and_assoc] using hs
  by_cases gbc : b.1 = c.1
  · have hh : b.1.1 ≠ a.1.1 := by
      intro hh; exact same ⟨hh.symm,hh.symm.trans (congrArg Prod.fst gbc)⟩
    have hxy : b.2 ≠ c.2 := fun he => bc (Prod.ext gbc he)
    obtain ⟨B,hB,hs⟩ := pair_cover hF b.1 a.1 hh b.2 c.2 a.2 hxy
    have hc : (b.1,c.2) = c := Prod.ext gbc rfl
    refine ⟨B,(class_subset H G L F).2.2.2 hB,?_⟩
    simpa only [hc,Prod.eta,insert_subset_iff,singleton_subset_iff,and_comm,and_left_comm,and_assoc] using hs
  · obtain ⟨B,hB,hs⟩ := h_cover hH a b c gab gac gbc
    exact ⟨B,(class_subset H G L F).1 hB,hs⟩

/-- Structural coverage of every triple, independent of the instance data. -/
theorem assembly_covers {u : ℕ} {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hH : HSeed H) (hG : GDDSeed G)
    (hL : IsCover L 4 3) (hF : Factors F) : Covers (assembly H G L F) 3 := by
  intro T hT
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := card_eq_three.mp hT
  cases x with
  | none =>
    cases y with
    | none => exact False.elim (hxy rfl)
    | some a =>
      cases z with
      | none => exact False.elim (hxz rfl)
      | some b => exact infinity_cover hG hL a b
  | some a =>
    cases y with
    | none =>
      cases z with
      | none => exact False.elim (hyz rfl)
      | some b => simpa only [insert_subset_iff,singleton_subset_iff,and_comm,and_left_comm,and_assoc] using infinity_cover (H := H) (F := F) hG hL a b
    | some b =>
      cases z with
      | none => simpa only [insert_subset_iff,singleton_subset_iff,and_comm,and_left_comm,and_assoc] using infinity_cover (H := H) (F := F) hG hL a b
      | some c =>
        exact core_cover (G := G) hH hL hF a b c
          (by simpa using hxy) (by simpa using hxz) (by simpa using hyz)

theorem assembly_isCover {u : ℕ} {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hH : HSeed H) (hG : GDDSeed G)
    (hL : IsCover L 4 3) (hF : Factors F) : IsCover (assembly H G L F) 4 3 :=
  ⟨assembly_uniform hH hG hL hF,assembly_covers hH hG hL hF⟩

end CoveringDesigns.QuadrupleAssembly
