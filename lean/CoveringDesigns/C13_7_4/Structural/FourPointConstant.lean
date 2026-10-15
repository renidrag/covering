import CoveringDesigns.C13_7_4.Structural.FourPoint
import CoveringDesigns.C13_7_4.Structural.FourPointCounting
import CoveringDesigns.C13_7_4.Structural.ResidualCount

/-! Excluding a constant selected column in the actual four-root star union. -/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural StantonGeometry

set_option maxHeartbeats 1600000

variable {α : Type*} [Fintype α] [DecidableEq α]

def rootStarUnion (C : Family α) (K : Finset α) : Family α := K.biUnion (star C)

def rootEdgeFamily (C : Family α) (K E : Finset α) : Family α :=
  C.filter (fun B => B ∩ K = E)

omit [Fintype α] in
theorem rootStarUnion_subset (C : Family α) (K : Finset α) : rootStarUnion C K ⊆ C := by
  intro B hB
  obtain ⟨p, _, hp⟩ := mem_biUnion.mp hB
  exact (mem_filter.mp hp).1

omit [Fintype α] in
theorem rootEdgeFamily_pairwise (C : Family α) (K : Finset α) :
    Pairwise fun E D => Disjoint (rootEdgeFamily C K E) (rootEdgeFamily C K D) := by
  intro E D hne
  apply disjoint_left.mpr
  intro B hBE hBD
  exact hne ((mem_filter.mp hBE).2.symm.trans (mem_filter.mp hBD).2)

omit [Fintype α] in
private theorem card_union_image_of_disjoint (K : Finset α) (R : Family α)
    (hdis : ∀ B ∈ R, Disjoint K B) : (R.image fun B => K ∪ B).card = R.card := by
  apply card_image_of_injOn
  intro B hB D hD he
  ext y
  by_cases hy : y ∈ K
  · have hb : y ∉ B := fun h => disjoint_left.mp (hdis B hB) hy h
    have hd : y ∉ D := fun h => disjoint_left.mp (hdis D hD) hy h
    simp [hb, hd]
  · have hm := congrArg (fun S => y ∈ S) he
    simpa only [mem_union, hy, false_or] using (Eq.to_iff hm)

namespace FourPointSystem

variable {C : Family α} {K : Finset α} (F : FourPointSystem C K)

/-- The intrinsic edge family, expressed in the shared triad coordinates. -/
theorem private_blocks (hK : K.card = 4) (p : α) (hp : p ∈ K)
    (q : α) (hq : q ∈ K) (hqp : q ≠ p) :
    rootEdgeFamily C K {p, q} =
      (insert (F.short p hp q hq hqp)
        (univ.image (markedRow F.common.triad (F.selected p hp q hq hqp)))).image
        (fun D => {p, q} ∪ D) := by
  have he := (F.vertex p hp).private_blocks hK (F.neighborIndex p hp q hq hqp)
  simpa [rootEdgeFamily, F.neighborIndex_spec, F.aligned, short, selected] using he

theorem trace_disjoint (hK : K.card = 4) (p : α) (hp : p ∈ K)
    (q : α) (hq : q ∈ K) (hqp : q ≠ p) :
    ∀ D ∈ insert (F.short p hp q hq hqp)
      (univ.image (markedRow F.common.triad (F.selected p hp q hq hqp))), Disjoint K D := by
  intro D hD
  rw [← F.private_traces hK p hp q hq hqp] at hD
  obtain ⟨B, _, rfl⟩ := mem_image.mp hD
  apply disjoint_left.mpr
  intro x hx hxs
  exact (mem_sdiff.mp hxs).2 hx

theorem short_additions_of_constant (j : Fin 3) (x : α)
    (hc : ∀ p hp q hq hqp, F.selected p hp q hq hqp j = x)
    (p : α) (hp : p ∈ K) (q : α) (hq : q ∈ K) (hqp : q ≠ p) :
    F.short p hp q hq hqp \ univ.image (F.selected p hp q hq hqp) =
      (F.common.triad j).erase x := by
  have hsel : ∀ r, (F.vertex p hp).selected r j = x := by
    intro r
    have h := hc p hp ((F.vertex p hp).neighbor r)
      ((F.vertex p hp).neighbor_mem r) ((F.vertex p hp).neighbor_ne r)
    have hi : F.neighborIndex p hp ((F.vertex p hp).neighbor r)
        ((F.vertex p hp).neighbor_mem r) ((F.vertex p hp).neighbor_ne r) = r :=
      (F.vertex p hp).neighbor_injective (F.neighborIndex_spec _ _ _ _ _)
    simpa only [selected, hi] using h
  have hh := (F.vertex p hp).common_additions j x hsel (F.neighborIndex p hp q hq hqp)
  simpa only [short, selected, F.aligned] using hh

theorem edge_degree_two_of_constant (hK : K.card = 4) (j : Fin 3) (x : α)
    (hc : ∀ p hp q hq hqp, F.selected p hp q hq hqp j = x)
    {E : Finset α} (hE : E ∈ K.powersetCard 2) {y : α}
    (hyK : y ∉ K) (hyA : y ∉ (F.common.triad j).erase x) :
    degree (rootEdgeFamily C K E) y = 2 := by
  obtain ⟨hEK, hEc⟩ := mem_powersetCard.mp hE
  obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp hEc
  have hp : p ∈ K := hEK (mem_insert_self _ _)
  have hq : q ∈ K := hEK (mem_insert_of_mem (mem_singleton_self _))
  have hd := F.trace_disjoint hK p hp q hq hpq.symm
  rw [F.private_blocks hK p hp q hq hpq.symm]
  rw [degree_union_image_of_disjoint {p, q} _ (fun B hB => (hd B hB).mono_left hEK)
    (fun h => hyK (hEK h))]
  exact trace_family_degree_two F.common (F.selected p hp q hq hpq.symm)
    (F.selected_mem p hp q hq hpq.symm) (F.short p hp q hq hpq.symm)
    ((F.common.triad j).erase x)
    (by intro z hz; obtain ⟨i, _, rfl⟩ := mem_image.mp hz
        exact F.selected_mem_short p hp q hq hpq.symm i)
    (F.short_additions_of_constant j x hc p hp q hq hpq.symm) hyK hyA

include F in
theorem edge_card_four (hK : K.card = 4) {E : Finset α}
    (hE : E ∈ K.powersetCard 2) : (rootEdgeFamily C K E).card = 4 := by
  obtain ⟨hEK, hEc⟩ := mem_powersetCard.mp hE
  obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp hEc
  have hp : p ∈ K := hEK (mem_insert_self _ _)
  have hq : q ∈ K := hEK (mem_insert_of_mem (mem_singleton_self _))
  have hd := F.trace_disjoint hK p hp q hq hpq.symm
  rw [F.private_blocks hK p hp q hq hpq.symm,
    card_union_image_of_disjoint _ _ (fun B hB => (hd B hB).mono_left hEK)]
  have hn : F.short p hp q hq hpq.symm ∉
      univ.image (markedRow F.common.triad (F.selected p hp q hq hpq.symm)) := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_image.mp h
    exact short_ne_markedRow F.common (F.selected p hp q hq hpq.symm)
      (F.selected_mem p hp q hq hpq.symm) (F.short p hp q hq hpq.symm)
      (F.selected_mem_short p hp q hq hpq.symm) i hi.symm
  rw [card_insert_of_notMem hn, card_image_of_injective _
    (triad_markedRow_injective F.common (F.selected p hp q hq hpq.symm)
      (F.selected_mem p hp q hq hpq.symm))]
  rfl

theorem common_edge_disjoint (hK : K.card = 4) {E : Finset α}
    (hE : E ∈ K.powersetCard 2) :
    Disjoint (univ.image fun j => K ∪ F.common.triad j) (rootEdgeFamily C K E) := by
  apply disjoint_left.mpr
  intro B hBc hBe
  obtain ⟨j, _, rfl⟩ := mem_image.mp hBc
  have he : K = E := by simpa using (mem_filter.mp hBe).2
  have hEc := (mem_powersetCard.mp hE).2
  have hh := congrArg Finset.card he
  omega

theorem rootStarUnion_decomposition (hK : K.card = 4) :
    rootStarUnion C K = (univ.image fun j => K ∪ F.common.triad j) ∪
      (K.powersetCard 2).biUnion (rootEdgeFamily C K) := by
  ext B
  constructor
  · intro hB
    obtain ⟨p, hp, hBp⟩ := mem_biUnion.mp hB
    rw [(F.vertex p hp).blocks_eq] at hBp
    rcases mem_union.mp hBp with hBp | hBp
    · rcases mem_union.mp hBp with hBc | hBm
      · apply mem_union_left
        simpa only [F.aligned] using hBc
      · obtain ⟨r, _, hBr⟩ := mem_biUnion.mp hBm
        obtain ⟨j, _, rfl⟩ := mem_image.mp hBr
        have hq := (F.vertex p hp).neighbor_mem r
        have hqp := (F.vertex p hp).neighbor_ne r
        apply mem_union_right
        refine mem_biUnion.mpr ⟨{p, (F.vertex p hp).neighbor r}, ?_, ?_⟩
        · apply mem_powersetCard.mpr
          exact ⟨by simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hp hq, by simp [hqp.symm]⟩
        · change _ ∈ C.filter _
          rw [(F.vertex p hp).private_blocks hK r]
          apply mem_image.mpr
          refine ⟨markedRow (F.vertex p hp).common.triad
            ((F.vertex p hp).selected r) j, ?_, rfl⟩
          exact mem_insert_of_mem (mem_image.mpr ⟨j, mem_univ _, rfl⟩)
    · obtain ⟨r, _, rfl⟩ := mem_image.mp hBp
      have hq := (F.vertex p hp).neighbor_mem r
      have hqp := (F.vertex p hp).neighbor_ne r
      apply mem_union_right
      refine mem_biUnion.mpr ⟨{p, (F.vertex p hp).neighbor r}, ?_, ?_⟩
      · apply mem_powersetCard.mpr
        exact ⟨by simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hp hq, by simp [hqp.symm]⟩
      · change _ ∈ C.filter _
        rw [(F.vertex p hp).private_blocks hK r]
        exact mem_image.mpr ⟨(F.vertex p hp).short r, mem_insert_self _ _, rfl⟩
  · intro hB
    rcases mem_union.mp hB with hBc | hBe
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hBc
      obtain ⟨p, hp⟩ := card_pos.mp (by omega : 0 < K.card)
      apply mem_biUnion.mpr
      refine ⟨p, hp, mem_filter.mpr ⟨?_, mem_union_left _ hp⟩⟩
      have hh := (F.vertex p hp).common_mem j
      simpa only [F.aligned] using hh
    · obtain ⟨E, hE, hBE⟩ := mem_biUnion.mp hBe
      obtain ⟨hEK, hEc⟩ := mem_powersetCard.mp hE
      obtain ⟨p, hp⟩ := card_pos.mp (by omega : 0 < E.card)
      have hBC := (mem_filter.mp hBE).1
      have he := (mem_filter.mp hBE).2
      refine mem_biUnion.mpr ⟨p, hEK hp, mem_filter.mpr ⟨hBC, ?_⟩⟩
      exact (mem_inter.mp (he ▸ hp)).1

theorem common_private_disjoint (hK : K.card = 4) :
    Disjoint (univ.image fun j => K ∪ F.common.triad j)
      ((K.powersetCard 2).biUnion (rootEdgeFamily C K)) := by
  apply disjoint_left.mpr
  intro B hBc hBp
  obtain ⟨E, hE, hBE⟩ := mem_biUnion.mp hBp
  exact disjoint_left.mp (F.common_edge_disjoint hK hE) hBc hBE

include F in
/-- The four stars consist of three common rows and four rows on each edge. -/
theorem rootStarUnion_card (hK : K.card = 4) : (rootStarUnion C K).card = 27 := by
  rw [F.rootStarUnion_decomposition hK,
    card_union_of_disjoint (F.common_private_disjoint hK),
    card_image_of_injective _ F.common.marked_injective]
  have hbi : ((K.powersetCard 2).biUnion (rootEdgeFamily C K)).card =
      ∑ E ∈ K.powersetCard 2, (rootEdgeFamily C K E).card := by
    apply card_biUnion
    intro E _ D _ hne
    exact rootEdgeFamily_pairwise C K hne
  rw [hbi]
  have hs : (∑ E ∈ K.powersetCard 2, (rootEdgeFamily C K E).card) =
      (K.powersetCard 2).card * 4 := by
    rw [sum_const_nat (fun E hE => F.edge_card_four hK hE)]
  rw [hs, card_powersetCard, hK]
  rfl

theorem rootStarUnion_degree_thirteen (hK : K.card = 4) (j : Fin 3) (x : α)
    (hc : ∀ p hp q hq hqp, F.selected p hp q hq hqp j = x)
    {y : α} (hyK : y ∉ K) (hyA : y ∉ (F.common.triad j).erase x) :
    degree (rootStarUnion C K) y = 13 := by
  rw [F.rootStarUnion_decomposition hK,
    degree_union_of_disjoint (F.common_private_disjoint hK),
    common_rows_degree_one F.common hyK]
  have hbi : degree ((K.powersetCard 2).biUnion (rootEdgeFamily C K)) y =
      ∑ E ∈ K.powersetCard 2, degree (rootEdgeFamily C K E) y := by
    unfold degree star
    rw [filter_biUnion]
    apply card_biUnion
    intro E _ D _ hne
    exact (rootEdgeFamily_pairwise C K hne).mono (filter_subset _ _) (filter_subset _ _)
  rw [hbi]
  have hs : (∑ E ∈ K.powersetCard 2, degree (rootEdgeFamily C K E) y) =
      (K.powersetCard 2).card * 2 := by
    rw [sum_const_nat (fun E hE => F.edge_degree_two_of_constant hK j x hc hE hyK hyA)]
  rw [hs, card_powersetCard, hK]
  rfl

end FourPointSystem

/-- A constant column forces seven points into both residual blocks, which
would make those two distinct seven-blocks equal. -/
theorem constant_column_impossible {C : Family α} {K : Finset α}
    (F : FourPointSystem C K) (hn : Fintype.card α = 13)
    (hC : IsCover C 7 4) (hb : C.card ≤ 29) (hK : K.card = 4)
    (j : Fin 3) (x : α)
    (hc : ∀ p hp q hq hqp, F.selected p hp q hq hqp j = x) : False := by
  obtain ⟨p, hp⟩ := card_pos.mp (by omega : 0 < K.card)
  let q := (F.vertex p hp).neighbor 0
  have hq : q ∈ K := (F.vertex p hp).neighbor_mem 0
  have hqp : q ≠ p := (F.vertex p hp).neighbor_ne 0
  have hxt : x ∈ F.common.triad j := by
    rw [← hc p hp q hq hqp]
    exact F.selected_mem p hp q hq hqp j
  let A := (F.common.triad j).erase x
  have hA : A.card = 2 := by
    rw [card_erase_of_mem hxt, F.common.triad_card]
  have hdis : Disjoint K A :=
    (F.common.disjoint_root j).mono_right (erase_subset _ _)
  let X : Finset α := univ \ (K ∪ A)
  have hX : X.card = 7 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn,
      card_union_of_disjoint hdis, hK, hA]
  apply residual_two_blocks_impossible (rootStarUnion_subset C K)
    (F.rootStarUnion_card hK) hb hC.1 hX
  · intro y hy
    have hh := (mem_sdiff.mp hy).2
    exact F.rootStarUnion_degree_thirteen hK j x hc
      (fun h => hh (mem_union_left _ h)) (fun h => hh (mem_union_right _ h))
  · intro y _
    exact degree_lower hn hC y

#guard_standard_axioms FourPointSystem.private_blocks
  FourPointSystem.short_additions_of_constant FourPointSystem.edge_degree_two_of_constant
  FourPointSystem.edge_card_four FourPointSystem.rootStarUnion_decomposition
  FourPointSystem.rootStarUnion_card FourPointSystem.rootStarUnion_degree_thirteen
  constant_column_impossible

end CoveringDesigns.C13Structural
