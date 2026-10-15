import CoveringDesigns.C13_7_4.Structural.GPPTGeometryHelpers

/-!
Intersection geometry derived from GPPT's structural reduction. The only
closed finite checks below concern the single printed Figure 1 core and the
single printed Figure 6 family. No completion or covering is enumerated.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Intersection bounds are unchanged by a point relabelling. -/
private theorem inter_bound_relabel (e : α ≃ β) {C : Family α} {k : ℕ}
    (h : ∀ A ∈ C, ∀ B ∈ C, A ≠ B → (A ∩ B).card ≤ k) :
    ∀ A ∈ CoveringDesigns.relabel e C, ∀ B ∈ CoveringDesigns.relabel e C,
      A ≠ B → (A ∩ B).card ≤ k := by
  rintro A hA B hB hne
  obtain ⟨A, hA0, rfl⟩ := mem_map.mp hA
  obtain ⟨B, hB0, rfl⟩ := mem_map.mp hB
  have hn : A ≠ B := fun he => hne (congrArg (Finset.map e.toEmbedding) he)
  change (A.map e.toEmbedding ∩ B.map e.toEmbedding).card ≤ k
  simpa only [← map_inter, card_map] using h A hA0 B hB0 hn

namespace OrdinaryGeometry

/-- Transport ordinary geometry along a point bijection. -/
def relabel (G : OrdinaryGeometry (C : Family α)) (e : α ≃ β) :
    OrdinaryGeometry (CoveringDesigns.relabel e C) where
  core := CoveringDesigns.relabel e G.core
  completed := CoveringDesigns.relabel e G.completed
  union_eq := by
    conv_lhs => rw [G.union_eq]
    exact map_union _ _
  disjoint := (disjoint_map _).mpr G.disjoint
  completed_card := (relabel_card _ _).trans G.completed_card
  core_card := (relabel_card _ _).trans G.core_card
  core_degree := by
    intro q
    obtain ⟨p, rfl⟩ := e.surjective q
    rw [degree_relabel, G.core_degree]
  core_inter := inter_bound_relabel e G.core_inter
  block_inter := inter_bound_relabel e G.block_inter

end OrdinaryGeometry

namespace ExceptionalGeometry

/-- Transport exceptional geometry along a point bijection. -/
def relabel (G : ExceptionalGeometry (C : Family α)) (e : α ≃ β) :
    ExceptionalGeometry (CoveringDesigns.relabel e C) where
  high := G.high.map e.toEmbedding
  high_card := (card_map _).trans G.high_card
  degree_high := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_map.mp hq
    change degree (CoveringDesigns.relabel e C) (e p) = 10
    rw [degree_relabel, G.degree_high p hp]
  degree_low := by
    intro q hq
    obtain ⟨p, rfl⟩ := e.surjective q
    have hp : p ∉ G.high := by simpa using hq
    rw [degree_relabel, G.degree_low p hp]
  high_columns := by
    intro A hA q hq hqA
    obtain ⟨A, hA0, rfl⟩ := mem_map.mp hA
    obtain ⟨p, hp, rfl⟩ := mem_map.mp hq
    have hpA : p ∈ A := by simpa using hqA
    exact map_subset_map.mpr (G.high_columns A hA0 p hp hpA)
  high_low := by
    intro p hp q hq
    obtain ⟨p, hp0, rfl⟩ := mem_map.mp hp
    obtain ⟨q, rfl⟩ := e.surjective q
    have hq : q ∉ G.high := by simpa using hq
    change degree (star (CoveringDesigns.relabel e C) (e p)) (e q) = 4
    rw [star_relabel, degree_relabel]
    exact G.high_low p hp0 q hq
  block_inter := inter_bound_relabel e G.block_inter
  inter_four := by
    rintro A hA B hB hne hi
    obtain ⟨A, hA0, rfl⟩ := mem_map.mp hA
    obtain ⟨B, hB0, rfl⟩ := mem_map.mp hB
    have hn : A ≠ B := fun h => hne (congrArg (Finset.map e.toEmbedding) h)
    change (A.map e.toEmbedding ∩ B.map e.toEmbedding).card = 4 at hi
    have hi0 : (A ∩ B).card = 4 := by simpa only [← map_inter, card_map] using hi
    change G.high.map e.toEmbedding ⊆ A.map e.toEmbedding ∩ B.map e.toEmbedding
    rw [← map_inter]
    exact map_subset_map.mpr (G.inter_four A hA0 B hB0 hn hi0)

end ExceptionalGeometry

/- Each of the fixed twelve full rows meets each spine in two points. -/
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem gppt_core_spine_inter : ∀ A ∈ core, ∀ i, (A ∩ spine i).card = 2 := by
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
theorem gppt_core_inter : ∀ A ∈ core, ∀ B ∈ core, A ≠ B → (A ∩ B).card ≤ 3 := by
  decide +kernel

theorem gppt_spines_disjoint : ∀ i j : Fin 3, i ≠ j → Disjoint (spine i) (spine j) := by
  decide +kernel

private theorem completed_uniform {R : Fin 3 → Finset (Fin 12)}
    (hR : ValidAdditions R) (i : Fin 3) : (spine i ∪ R i).card = 6 := by
  have hd : Disjoint (spine i) (R i) := by
    apply disjoint_left.mpr
    intro x hx hxR
    exact (mem_sdiff.mp ((hR i).1 hxR)).2 hx
  rw [card_union_of_disjoint hd, spine_card, (hR i).2]

private theorem completed_injective {R : Fin 3 → Finset (Fin 12)}
    (hR : ValidAdditions R) : Function.Injective (fun i => spine i ∪ R i) := by
  intro i j he
  change spine i ∪ R i = spine j ∪ R j at he
  by_contra hij
  have hs : spine i ∪ spine j ⊆ spine i ∪ R i := by
    apply union_subset
    · exact subset_union_left
    · rw [he]
      exact subset_union_left
  have hc := card_le_card hs
  rw [card_union_of_disjoint (gppt_spines_disjoint i j hij), spine_card, spine_card,
    completed_uniform hR] at hc
  omega

private theorem core_completed_disjoint {R : Fin 3 → Finset (Fin 12)}
    (_hR : ValidAdditions R) :
    Disjoint core (univ.image (fun i => spine i ∪ R i)) := by
  apply disjoint_left.mpr
  intro A hA hE
  obtain ⟨i, _, rfl⟩ := mem_image.mp hE
  have hi := gppt_core_spine_inter _ hA i
  rw [union_inter_cancel_left, spine_card] at hi
  omega

private theorem core_completed_inter {R : Fin 3 → Finset (Fin 12)}
    (hR : ValidAdditions R) {A : Finset (Fin 12)} (hA : A ∈ core) (i : Fin 3) :
    (A ∩ (spine i ∪ R i)).card ≤ 4 := by
  rw [inter_union_distrib_left]
  have hc := card_union_le (A ∩ spine i) (A ∩ R i)
  have hR' := card_le_card (inter_subset_right (s₁ := A) (s₂ := R i))
  rw [gppt_core_spine_inter A hA i] at hc
  rw [(hR i).2] at hR'
  omega

private theorem completed_completed_inter {R : Fin 3 → Finset (Fin 12)}
    (hR : ValidAdditions R) {i j : Fin 3} (hij : i ≠ j) :
    ((spine i ∪ R i) ∩ (spine j ∪ R j)).card ≤ 4 := by
  have hs : (spine i ∪ R i) ∩ (spine j ∪ R j) ⊆ R i ∪ R j := by
    intro x hx
    obtain ⟨hi, hj⟩ := mem_inter.mp hx
    rcases mem_union.mp hi with hi | hi
    · rcases mem_union.mp hj with hj | hj
      · exact False.elim (disjoint_left.mp (gppt_spines_disjoint i j hij) hi hj)
      · exact mem_union_right _ hj
    · exact mem_union_left _ hi
  have hc := card_le_card hs
  have hu := card_union_le (R i) (R j)
  rw [(hR i).2, (hR j).2] at hu
  omega

/-- Every valid spine completion has ordinary geometry, without enumerating
any possible completion. -/
def template_geometry {R : Fin 3 → Finset (Fin 12)} (hR : ValidAdditions R) :
    OrdinaryGeometry (templateBlocks R) where
  core := core
  completed := univ.image (fun i => spine i ∪ R i)
  union_eq := rfl
  disjoint := core_completed_disjoint hR
  completed_card := by rw [card_image_of_injective _ (completed_injective hR)]; rfl
  core_card := GPPTStructural.core_card
  core_degree := core_degree
  core_inter := gppt_core_inter
  block_inter := by
    intro A hA B hB hne
    rcases mem_union.mp hA with hA | hA
    · rcases mem_union.mp hB with hB | hB
      · exact (gppt_core_inter A hA B hB hne).trans (by decide)
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hB
        exact core_completed_inter hR hA i
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hA
      rcases mem_union.mp hB with hB | hB
      · rw [inter_comm]
        exact core_completed_inter hR hB i
      · obtain ⟨j, _, rfl⟩ := mem_image.mp hB
        have hij : i ≠ j := fun h => hne (congrArg (fun i => spine i ∪ R i) h)
        exact completed_completed_inter hR hij

/- Only the literal Figure 6 family is inspected in this closed kernel check. -/
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
def figure6_geometry : ExceptionalGeometry figure6 where
  high := {4, 5}
  high_card := by decide +kernel
  degree_high := by decide +kernel
  degree_low := by decide +kernel
  high_columns := by decide +kernel
  high_low := by decide +kernel
  block_inter := by decide +kernel
  inter_four := by decide +kernel

/-- Geometry survives any isomorphism to an ordinary completion. -/
theorem ordinary_geometry_of_isomorphic {C : Family α} {D : Family (Fin 12)}
    (hD : IsTemplateCompletion D) (he : Isomorphic C D) : Nonempty (OrdinaryGeometry C) := by
  obtain ⟨R, hR, rfl⟩ := hD
  obtain ⟨e, he⟩ := he
  have h := (template_geometry hR).relabel e.symm
  rw [← he, relabel_symm_relabel] at h
  exact ⟨h⟩

theorem exceptional_geometry_of_isomorphic {C : Family α}
    (he : Isomorphic C figure6) : Nonempty (ExceptionalGeometry C) := by
  obtain ⟨e, he⟩ := he
  have h := figure6_geometry.relabel e.symm
  rw [← he, relabel_symm_relabel] at h
  exact ⟨h⟩

/-- The reusable geometric consequence of GPPT Theorem 5.9. -/
theorem minimum_geometry [Fintype α] {C : Family α} (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hb : C.card = 15) :
    Nonempty (OrdinaryGeometry C) ∨ Nonempty (ExceptionalGeometry C) := by
  let e : α ≃ Fin 12 := Fintype.equivFinOfCardEq hn
  have hD : IsCover (CoveringDesigns.relabel e C) 6 3 := relabel_isCover e hC
  have hcard : (CoveringDesigns.relabel e C).card = 15 := (relabel_card e C).trans hb
  rcases gppt_structural_reduction hD hcard with ho | he
  · obtain ⟨D, hD, f, hf⟩ := ho
    apply Or.inl
    exact ordinary_geometry_of_isomorphic hD ⟨e.trans f, by rw [← relabel_trans, hf]⟩
  · apply Or.inr
    exact exceptional_geometry_of_isomorphic (Isomorphic.trans ⟨e, rfl⟩ he)

/-- The structural alternatives also give the sharp degree upper bound ten. -/
theorem minimum_degree_le_ten [Fintype α] {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card = 15) (p : α) :
    degree C p ≤ 10 := by
  rcases minimum_geometry hn hC hb with h | h
  · obtain ⟨G⟩ := h
    exact (G.degree_le_nine p).trans (by decide)
  · obtain ⟨G⟩ := h
    exact G.degree_le_ten p

/-- Distinct rows in any minimum (12,6,3) cover intersect in at most four. -/
theorem minimum_block_inter_le_four [Fintype α] {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card = 15)
    {A B : Finset α} (hA : A ∈ C) (hB : B ∈ C) (hne : A ≠ B) :
    (A ∩ B).card ≤ 4 := by
  rcases minimum_geometry hn hC hb with h | h
  · obtain ⟨G⟩ := h
    exact G.block_inter A hA B hB hne
  · obtain ⟨G⟩ := h
    exact G.block_inter A hA B hB hne

#guard_standard_axioms gppt_core_spine_inter gppt_core_inter gppt_spines_disjoint
  ordinary_geometry_of_isomorphic exceptional_geometry_of_isomorphic minimum_geometry
  minimum_degree_le_ten minimum_block_inter_le_four

end CoveringDesigns.C13Structural
