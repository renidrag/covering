import CoveringDesigns.C13_7_4.Structural.FourPointFrames
import CoveringDesigns.C13_7_4.Structural.SelectedFrame
import CoveringDesigns.C13_7_4.Structural.K4Coloring

/-! The six compatible Stanton frames on a four-point root set. -/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural StantonGeometry

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 800000

/-- A triad partition, shared by the four prescribed minimum-point links. -/
structure FourPointSystem [Fintype α] (C : Family α) (K : Finset α) where
  common : RootTriads K
  vertex : ∀ p, p ∈ K → FourPointVertex C p K
  aligned : ∀ p hp, (vertex p hp).common.triad = common.triad

/-- GPPT frames at the four roots can all be put in the same triad coordinates. -/
theorem exists_fourPointSystem [Fintype α] {C : Family α} {K : Finset α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hK : K.card = 4)
    (hthree : containmentCount C K = 3)
    (hmin : ∀ p ∈ K, degree C p = 15)
    (hpair : ∀ p ∈ K, ∀ q ∈ K, p ≠ q → degree (star C p) q = 7) :
    Nonempty (FourPointSystem C K) := by
  classical
  have hex (p : α) (hp : p ∈ K) : Nonempty (FourPointVertex C p K) :=
    exists_fourPointVertex hn hC hK hthree hp (hmin p hp)
      (fun q hq hqp => hpair p hp q hq hqp.symm)
  let F (p : α) (hp : p ∈ K) := Classical.choice (hex p hp)
  obtain ⟨p, hp⟩ := card_pos.mp (by omega : 0 < K.card)
  let G := (F p hp).common
  have halign (q : α) (hq : q ∈ K) :
      ∃ H : FourPointVertex C q K, H.common.triad = G.triad :=
    (F q hq).exists_aligned G (F p hp).common_mem hthree
  choose H hH using halign
  exact ⟨⟨G, H, hH⟩⟩

private theorem disjoint_markedRow {K : Finset α} (T : Fin 3 → Finset α)
    (s : Fin 3 → α) (hd : ∀ j, Disjoint K (T j))
    (hs : ∀ j, s j ∈ T j) (i : Fin 3) :
    Disjoint K (markedRow T s i) := by
  apply disjoint_left.mpr
  intro x hx hy
  rcases mem_union.mp hy with hy | hy
  · have he := mem_singleton.mp hy
    exact disjoint_left.mp (hd i) hx (he ▸ hs i)
  · obtain ⟨j, _, hy⟩ := mem_biUnion.mp hy
    exact disjoint_left.mp (hd j) hx (mem_sdiff.mp hy).1

private theorem private_inter_root {K D : Finset α} {p q : α}
    (hp : p ∈ K) (hq : q ∈ K) (hd : Disjoint K D) :
    insert p (insert q D) ∩ K = {p, q} := by
  ext x
  have hn := disjoint_left.mp hd
  simp only [mem_inter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h | h | h, hx⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn hx h)
  · rintro (rfl | rfl) <;> simp_all

private theorem private_sdiff_root {K D : Finset α} {p q : α}
    (hp : p ∈ K) (hq : q ∈ K) (hd : Disjoint K D) :
    insert p (insert q D) \ K = D := by
  ext x
  have hn := disjoint_left.mp hd
  simp only [mem_sdiff, mem_insert]
  constructor
  · rintro ⟨h | h | h, hx⟩
    · exact False.elim (hx (h ▸ hp))
    · exact False.elim (hx (h ▸ hq))
    · exact h
  · intro hx
    exact ⟨Or.inr (Or.inr hx), fun h => hn h hx⟩

namespace FourPointVertex

variable [Fintype α] {C : Family α} {p : α} {K : Finset α}
  (F : FourPointVertex C p K)

/-- The four noncommon blocks at an edge are determined by its exact root
intersection, independently of which endpoint supplied its GPPT frame. -/
theorem private_blocks (hK : K.card = 4) (r : Fin 3) :
    C.filter (fun B => B ∩ K = {p, F.neighbor r}) =
      (insert (F.short r) (univ.image (markedRow F.common.triad (F.selected r)))).image
        (fun D => insert p (insert (F.neighbor r) D)) := by
  have hshort := F.short_disjoint r
  have hmarked (j : Fin 3) := disjoint_markedRow F.common.triad
    (F.selected r) F.common.disjoint_root (F.selected_mem r) j
  have hcard : ({p, F.neighbor r} : Finset α).card = 2 := by
    simp [Ne.symm (F.neighbor_ne r)]
  have hcommon (j : Fin 3) : (K ∪ F.common.triad j) ∩ K ≠ {p, F.neighbor r} := by
    rw [union_inter_distrib_right, inter_self]
    intro he
    have hh : K = {p, F.neighbor r} := by
      simpa only [union_eq_left.mpr inter_subset_right] using he
    have hc := congrArg Finset.card hh
    omega
  ext B
  constructor
  · intro hB
    obtain ⟨hBC, hi⟩ := mem_filter.mp hB
    have hpB : p ∈ B := (mem_inter.mp (hi ▸ (mem_insert_self p {F.neighbor r}))).1
    have hqB : F.neighbor r ∈ B :=
      (mem_inter.mp (hi ▸ (mem_insert_of_mem (mem_singleton_self _)))).1
    have hm : B ∈ star (star C p) (F.neighbor r) :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨hBC, hpB⟩, hqB⟩
    rw [F.pair_blocks] at hm
    rcases mem_insert.mp hm with rfl | hm
    · exact mem_image.mpr ⟨F.short r, mem_insert_self _ _, rfl⟩
    rcases mem_union.mp hm with hm | hm
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hm
      exact False.elim (hcommon j hi)
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hm
      exact mem_image.mpr ⟨markedRow F.common.triad (F.selected r) j,
        mem_insert_of_mem (mem_image.mpr ⟨j, mem_univ _, rfl⟩), rfl⟩
  · intro hB
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hB
    rcases mem_insert.mp hD with rfl | hD
    · refine mem_filter.mpr ⟨?_, private_inter_root F.root_mem (F.neighbor_mem r) hshort⟩
      have hm : insert p (insert (F.neighbor r) (F.short r)) ∈
          star (star C p) (F.neighbor r) := by
        rw [F.pair_blocks]
        exact mem_insert_self _ _
      exact (mem_filter.mp (mem_filter.mp hm).1).1
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hD
      exact mem_filter.mpr ⟨F.marked_mem r j,
        private_inter_root F.root_mem (F.neighbor_mem r) (hmarked j)⟩

/-- Erasing the root set recovers exactly the four Stanton traces of an edge. -/
theorem private_traces (hK : K.card = 4) (r : Fin 3) :
    (C.filter (fun B => B ∩ K = {p, F.neighbor r})).image (fun B => B \ K) =
      insert (F.short r) (univ.image (markedRow F.common.triad (F.selected r))) := by
  rw [F.private_blocks hK r, image_image]
  trans (insert (F.short r) (univ.image (markedRow F.common.triad (F.selected r)))).image id
  · apply image_congr
    intro D hD
    rcases mem_insert.mp hD with rfl | hD
    · exact private_sdiff_root F.root_mem (F.neighbor_mem r) (F.short_disjoint r)
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hD
      exact private_sdiff_root F.root_mem (F.neighbor_mem r)
        (disjoint_markedRow F.common.triad (F.selected r)
          F.common.disjoint_root (F.selected_mem r) j)
  · simp only [image_id]

end FourPointVertex

namespace FourPointSystem

variable [Fintype α] {C : Family α} {K : Finset α} (F : FourPointSystem C K)

noncomputable def neighborIndex (p : α) (hp : p ∈ K) (q : α) (hq : q ∈ K)
    (hqp : q ≠ p) : Fin 3 :=
  Classical.choose ((F.vertex p hp).neighbor_surjective hq hqp)

theorem neighborIndex_spec (p : α) (hp : p ∈ K) (q : α) (hq : q ∈ K)
    (hqp : q ≠ p) :
    (F.vertex p hp).neighbor (F.neighborIndex p hp q hq hqp) = q :=
  Classical.choose_spec ((F.vertex p hp).neighbor_surjective hq hqp)

noncomputable def selected (p : α) (hp : p ∈ K) (q : α) (hq : q ∈ K)
    (hqp : q ≠ p) : Fin 3 → α :=
  (F.vertex p hp).selected (F.neighborIndex p hp q hq hqp)

noncomputable def short (p : α) (hp : p ∈ K) (q : α) (hq : q ∈ K)
    (hqp : q ≠ p) : Finset α :=
  (F.vertex p hp).short (F.neighborIndex p hp q hq hqp)

theorem selected_mem (p : α) (hp : p ∈ K) (q : α) (hq : q ∈ K)
    (hqp : q ≠ p) (j : Fin 3) : F.selected p hp q hq hqp j ∈ F.common.triad j := by
  simpa only [selected, F.aligned] using
    (F.vertex p hp).selected_mem (F.neighborIndex p hp q hq hqp) j

theorem selected_mem_short (p : α) (hp : p ∈ K) (q : α) (hq : q ∈ K)
    (hqp : q ≠ p) (j : Fin 3) : F.selected p hp q hq hqp j ∈ F.short p hp q hq hqp :=
  (F.vertex p hp).selected_subset (F.neighborIndex p hp q hq hqp)
    (mem_image.mpr ⟨j, mem_univ _, rfl⟩)

theorem private_traces (hK : K.card = 4) (p : α) (hp : p ∈ K)
    (q : α) (hq : q ∈ K) (hqp : q ≠ p) :
    (C.filter (fun B => B ∩ K = {p, q})).image (fun B => B \ K) =
      insert (F.short p hp q hq hqp)
        (univ.image (markedRow F.common.triad (F.selected p hp q hq hqp))) := by
  have he := (F.vertex p hp).private_traces hK (F.neighborIndex p hp q hq hqp)
  simpa only [F.neighborIndex_spec, F.aligned, short, selected] using he

/-- The selection on an edge is the same from either of its endpoint links. -/
theorem selected_symm (hK : K.card = 4) (p : α) (hp : p ∈ K)
    (q : α) (hq : q ∈ K) (hqp : q ≠ p) :
    F.selected p hp q hq hqp = F.selected q hq p hp hqp.symm := by
  apply selected_eq_of_rows_eq F.common.triad _ _
    (F.short p hp q hq hqp) (F.short q hq p hp hqp.symm)
    F.common.triad_card F.common.pairwise_disjoint
    (F.selected_mem p hp q hq hqp) (F.selected_mem q hq p hp hqp.symm)
    (F.selected_mem_short p hp q hq hqp) (F.selected_mem_short q hq p hp hqp.symm)
  rw [← F.private_traces hK p hp q hq hqp,
    ← F.private_traces hK q hq p hp hqp.symm]
  simp only [pair_comm]

end FourPointSystem

#guard_standard_axioms exists_fourPointSystem FourPointVertex.private_blocks
  FourPointVertex.private_traces FourPointSystem.selected_symm

end CoveringDesigns.C13Structural
