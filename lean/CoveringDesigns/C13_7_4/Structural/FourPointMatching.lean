import CoveringDesigns.C13_7_4.Structural.SelectedFrame
import CoveringDesigns.C13_7_4.Structural.GPPTGeometryHelpers
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Two opposite-edge matchings of a four-point root set produce four disjoint
pairs of rows with intersection four in a fifth point's link. The argument
uses marked-trace intersections and the root sets of the rows, independently
of the additions to any short trace.
-/

namespace CoveringDesigns.C13Structural

open Finset StantonGeometry

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1200000

/-- Every point of a marked trace belongs to one of its three triads. -/
theorem markedRow_mem_some_triad (T : Fin 3 → Finset α) (s : Fin 3 → α)
    (hs : ∀ j, s j ∈ T j) {i : Fin 3} {x : α}
    (hx : x ∈ markedRow T s i) : ∃ j, x ∈ T j := by
  rcases mem_union.mp hx with hx | hx
  · obtain rfl := mem_singleton.mp hx
    exact ⟨i, hs i⟩
  · obtain ⟨j, _, hj⟩ := mem_biUnion.mp hx
    exact ⟨j, (mem_sdiff.mp hj).1⟩

/-- Marked traces have size five: one selected point and two mates in each
of the other two triads. -/
theorem markedRow_card_five (T : Fin 3 → Finset α) (s : Fin 3 → α)
    (hcard : ∀ j, (T j).card = 3)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hs : ∀ j, s j ∈ T j) (i : Fin 3) : (markedRow T s i).card = 5 := by
  have hparts (j : Fin 3) : (T j \ {s j}).card = 2 := by
    rw [card_sdiff_of_subset (singleton_subset_iff.mpr (hs j)), hcard]
    simp
  have h0 : Disjoint ({s i} : Finset α)
      ((univ.erase i).biUnion fun j => T j \ {s j}) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain rfl := mem_singleton.mp hx
    obtain ⟨j, hj, hy⟩ := mem_biUnion.mp hy
    exact disjoint_left.mp (hdis (mem_erase.mp hj).1) (mem_sdiff.mp hy).1 (hs i)
  rw [markedRow, card_union_of_disjoint h0, card_singleton,
    card_biUnion (fun j _ k _ hjk =>
      (hdis hjk).mono sdiff_subset sdiff_subset)]
  simp_rw [hparts]
  simp

/-- Distinct triad labels give distinct marked traces. -/
theorem markedRow_injective (T : Fin 3 → Finset α) (s : Fin 3 → α)
    (hcard : ∀ j, (T j).card = 3)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hs : ∀ j, s j ∈ T j) : Function.Injective (markedRow T s) := by
  intro i j he
  by_contra hij
  have hh := congrArg (fun B => (B ∩ T i).card) he
  rw [markedRow_inter_self_triad T s hdis hs,
    markedRow_inter_other_triad T s hdis hs (Ne.symm hij), card_singleton,
    card_sdiff_of_subset (singleton_subset_iff.mpr (hs i)), hcard] at hh
  simp at hh

/-- The two traces whose labels are one and two share exactly the two
unselected points of triad zero. -/
theorem markedRow_one_inter_two (T : Fin 3 → Finset α) (s : Fin 3 → α)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hs : ∀ j, s j ∈ T j) :
    markedRow T s 1 ∩ markedRow T s 2 = T 0 \ {s 0} := by
  ext x
  constructor
  · intro hx
    obtain ⟨h1, h2⟩ := mem_inter.mp hx
    obtain ⟨j, hxT⟩ := markedRow_mem_some_triad T s hs h1
    fin_cases j
    · have hx' : x ∈ markedRow T s 1 ∩ T 0 := mem_inter.mpr ⟨h1, hxT⟩
      rwa [markedRow_inter_other_triad T s hdis hs (by decide : (1 : Fin 3) ≠ 0)] at hx'
    · have hx' : x ∈ markedRow T s 1 ∩ T 1 := mem_inter.mpr ⟨h1, hxT⟩
      rw [markedRow_inter_self_triad T s hdis hs] at hx'
      have hy : x ∈ markedRow T s 2 ∩ T 1 := mem_inter.mpr ⟨h2, hxT⟩
      rw [markedRow_inter_other_triad T s hdis hs (by decide : (2 : Fin 3) ≠ 1)] at hy
      exact False.elim ((mem_sdiff.mp hy).2 hx')
    · have hx' : x ∈ markedRow T s 2 ∩ T 2 := mem_inter.mpr ⟨h2, hxT⟩
      rw [markedRow_inter_self_triad T s hdis hs] at hx'
      have hy : x ∈ markedRow T s 1 ∩ T 2 := mem_inter.mpr ⟨h1, hxT⟩
      rw [markedRow_inter_other_triad T s hdis hs (by decide : (1 : Fin 3) ≠ 2)] at hy
      exact False.elim ((mem_sdiff.mp hy).2 hx')
  · intro hx
    have h1 : x ∈ markedRow T s 1 ∩ T 0 := by
      rwa [markedRow_inter_other_triad T s hdis hs (by decide : (1 : Fin 3) ≠ 0)]
    have h2 : x ∈ markedRow T s 2 ∩ T 0 := by
      rwa [markedRow_inter_other_triad T s hdis hs (by decide : (2 : Fin 3) ≠ 0)]
    exact mem_inter.mpr ⟨(mem_inter.mp h1).1, (mem_inter.mp h2).1⟩

/-- Index the four opposite-root-edge pairs by matching and trace label. -/
abbrev fourMatchingIndex : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv (m := 2) (n := 2)).symm

/-- All three canonical perfect matchings, in order 01/23, 02/13, 03/12. -/
def canonicalEdge (v : Fin 4 → α) (i : Fin 3 × Bool) : Finset α :=
  if i.1 = 0 then
    if i.2 then {v 2, v 3} else {v 0, v 1}
  else if i.1 = 1 then
    if i.2 then {v 1, v 3} else {v 0, v 2}
  else
    if i.2 then {v 1, v 2} else {v 0, v 3}

/-- The six canonical edges are distinct when the four roots are distinct. -/
theorem canonicalEdge_injective {v : Fin 4 → α} (hv : Function.Injective v) :
    Function.Injective (canonicalEdge v) := by
  intro ⟨i, b⟩ ⟨j, c⟩ he
  have hi (k l : Fin 4) : v k = v l ↔ k = l := hv.eq_iff
  have h0 := congrArg (fun B => v 0 ∈ B) he
  have h1 := congrArg (fun B => v 1 ∈ B) he
  have h2 := congrArg (fun B => v 2 ∈ B) he
  have h3 := congrArg (fun B => v 3 ∈ B) he
  clear he
  fin_cases i <;> cases b <;> fin_cases j <;> cases c <;>
    simp_all [canonicalEdge]

/-- The two edges in a canonical matching are disjoint. -/
theorem canonicalEdge_opposite_disjoint {v : Fin 4 → α} (hv : Function.Injective v)
    (i : Fin 3) : Disjoint (canonicalEdge v (i, false)) (canonicalEdge v (i, true)) := by
  have hi (k l : Fin 4) : v k = v l ↔ k = l := hv.eq_iff
  fin_cases i <;> simp [canonicalEdge, disjoint_left, hi]

/-- Every canonical edge consists of roots. -/
theorem canonicalEdge_subset_roots (v : Fin 4 → α) (i : Fin 3 × Bool) :
    canonicalEdge v i ⊆ univ.image v := by
  have hm (r : Fin 4) : v r ∈ univ.image v := mem_image.mpr ⟨r, mem_univ _, rfl⟩
  obtain ⟨i, b⟩ := i
  fin_cases i <;> cases b <;> simp [canonicalEdge, insert_subset_iff, singleton_subset_iff, hm]

/-- Root-triad separation is inherited by every canonical edge. -/
theorem canonicalEdge_disjoint_triads (v : Fin 4 → α) (T : Fin 3 → Finset α)
    (hroot : ∀ r j, v r ∉ T j) (i : Fin 3 × Bool) (j : Fin 3) :
    Disjoint (canonicalEdge v i) (T j) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨r, _, rfl⟩ := mem_image.mp (canonicalEdge_subset_roots v i hx)
  exact hroot r j hy

/-- The eight global rows, before deleting their shared outside point. -/
def fourPointGlobalBlock (E : Fin 2 × Bool → Finset α)
    (T : Fin 3 → Finset α) (S : Fin 2 → Fin 3 → α)
    (i : (Fin 2 × Fin 2) × Bool) : Finset α :=
  E (i.1.1, i.2) ∪ markedRow T (S i.1.1) i.1.2.succ

private theorem root_union_disjoint_marked
    (E : Fin 2 × Bool → Finset α) (T : Fin 3 → Finset α)
    (S : Fin 2 → Fin 3 → α)
    (hET : ∀ e j, Disjoint (E e) (T j))
    (hs : ∀ m j, S m j ∈ T j) (m : Fin 2) (j : Fin 3) :
    Disjoint (univ.biUnion E) (markedRow T (S m) j) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨e, _, he⟩ := mem_biUnion.mp hx
  obtain ⟨k, hk⟩ := markedRow_mem_some_triad T (S m) (hs m) hy
  exact disjoint_left.mp (hET e k) he hk

/-- Intersecting a global row with the root set recovers its edge. -/
private theorem fourPointGlobalBlock_inter_roots
    (E : Fin 2 × Bool → Finset α) (T : Fin 3 → Finset α)
    (S : Fin 2 → Fin 3 → α)
    (hET : ∀ e j, Disjoint (E e) (T j))
    (hs : ∀ m j, S m j ∈ T j) (i : (Fin 2 × Fin 2) × Bool) :
    fourPointGlobalBlock E T S i ∩ univ.biUnion E = E (i.1.1, i.2) := by
  have he : E (i.1.1, i.2) ⊆ univ.biUnion E :=
    fun _ hx => mem_biUnion.mpr ⟨_, mem_univ _, hx⟩
  have hd := root_union_disjoint_marked E T S hET hs i.1.1 i.1.2.succ
  rw [fourPointGlobalBlock, union_inter_distrib_right, inter_eq_left.mpr he,
    disjoint_iff_inter_eq_empty.mp hd.symm, union_empty]

/-- Removing the roots from a global row recovers its marked trace. -/
private theorem fourPointGlobalBlock_sdiff_roots
    (E : Fin 2 × Bool → Finset α) (T : Fin 3 → Finset α)
    (S : Fin 2 → Fin 3 → α)
    (hET : ∀ e j, Disjoint (E e) (T j))
    (hs : ∀ m j, S m j ∈ T j) (i : (Fin 2 × Fin 2) × Bool) :
    fourPointGlobalBlock E T S i \ univ.biUnion E = markedRow T (S i.1.1) i.1.2.succ := by
  have he : E (i.1.1, i.2) ⊆ univ.biUnion E :=
    fun _ hx => mem_biUnion.mpr ⟨_, mem_univ _, hx⟩
  rw [fourPointGlobalBlock, union_sdiff_distrib,
    sdiff_eq_empty_iff_subset.mpr he, empty_union]
  exact sdiff_eq_self_of_disjoint
    (root_union_disjoint_marked E T S hET hs i.1.1 i.1.2.succ).symm

/-- Distinct root edges distinguish rows in different edge families; trace
labels distinguish the two rows in one family. -/
theorem fourPointGlobalBlock_injective
    (E : Fin 2 × Bool → Finset α) (T : Fin 3 → Finset α)
    (S : Fin 2 → Fin 3 → α)
    (hE : Function.Injective E)
    (hET : ∀ e j, Disjoint (E e) (T j))
    (hcard : ∀ j, (T j).card = 3)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hs : ∀ m j, S m j ∈ T j) :
    Function.Injective (fourPointGlobalBlock E T S) := by
  rintro ⟨⟨m, k⟩, b⟩ ⟨⟨n, l⟩, c⟩ he
  have hroot := congrArg (fun B => B ∩ univ.biUnion E) he
  simp only [fourPointGlobalBlock_inter_roots E T S hET hs] at hroot
  have hmc := hE hroot
  have hmn : m = n := congrArg Prod.fst hmc
  have hbc : b = c := congrArg Prod.snd hmc
  subst n
  subst c
  have htrace := congrArg (fun B => B \ univ.biUnion E) he
  simp only [fourPointGlobalBlock_sdiff_roots E T S hET hs] at htrace
  have hkl := markedRow_injective T (S m) hcard hdis (hs m) htrace
  have hkl' : k = l := by simpa using hkl
  subst l
  rfl

/-- Opposite edges have no common root, so their two rows intersect in the
shared five-point marked trace. -/
theorem fourPointGlobalBlock_opposite_inter
    (E : Fin 2 × Bool → Finset α) (T : Fin 3 → Finset α)
    (S : Fin 2 → Fin 3 → α)
    (hE : ∀ m, Disjoint (E (m, false)) (E (m, true)))
    (m k : Fin 2) :
    fourPointGlobalBlock E T S ((m, k), false) ∩
      fourPointGlobalBlock E T S ((m, k), true) = markedRow T (S m) k.succ := by
  rw [fourPointGlobalBlock, fourPointGlobalBlock, ← inter_union_distrib_right,
    disjoint_iff_inter_eq_empty.mp (hE m), empty_union]

/-- Two opposite-edge matchings, with both selected points different from
`p` in triad zero, force four distinct intersection-four row pairs in its
link. The common intersection of all endpoints has size at most one. -/
theorem exists_four_point_matching
    (C : Family α) (p : α) (E : Fin 2 × Bool → Finset α)
    (T : Fin 3 → Finset α) (S : Fin 2 → Fin 3 → α)
    (hE : Function.Injective E)
    (hop : ∀ m, Disjoint (E (m, false)) (E (m, true)))
    (hET : ∀ e j, Disjoint (E e) (T j))
    (hcard : ∀ j, (T j).card = 3)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hs : ∀ m j, S m j ∈ T j) (hp : p ∈ T 0)
    (hsp : ∀ m, S m 0 ≠ p)
    (hmem : ∀ i, fourPointGlobalBlock E T S i ∈ C) :
    ∃ M : IntersectionFourMatching (link C p) 4,
      ∀ H : Finset {x : α // x ≠ p}, (∀ i, H ⊆ M.block i) → H.card ≤ 1 := by
  let D := fourPointGlobalBlock E T S
  let e : Fin 4 × Bool ≃ (Fin 2 × Fin 2) × Bool :=
    fourMatchingIndex.prodCongr (Equiv.refl Bool)
  have hpin (m k : Fin 2) : p ∈ markedRow T (S m) k.succ := by
    have hpm : p ∈ T 0 \ {S m 0} := by
      simp only [mem_sdiff, mem_singleton]
      exact ⟨hp, Ne.symm (hsp m)⟩
    have hm : p ∈ markedRow T (S m) k.succ ∩ T 0 := by
      rwa [markedRow_inter_other_triad T (S m) hdis (hs m) (Fin.succ_ne_zero k)]
    exact (mem_inter.mp hm).1
  have hthrough (i) : p ∈ D i := mem_union_right _ (hpin i.1.1 i.1.2)
  have hd_inj : Function.Injective D :=
    fourPointGlobalBlock_injective E T S hE hET hcard hdis hs
  let B := fun i => (D i).subtype (· ≠ p)
  have hb_inj : Function.Injective B := by
    intro i j hij
    exact hd_inj ((subtype_ne_inj (hthrough i) (hthrough j)).mp hij)
  have hb_mem (i) : B i ∈ link C p :=
    mem_image.mpr ⟨D i, mem_filter.mpr ⟨hmem i, hthrough i⟩, rfl⟩
  have hb_inter (m k : Fin 2) :
      (B ((m, k), false) ∩ B ((m, k), true)).card = 4 := by
    change (((D ((m, k), false)).subtype (· ≠ p)) ∩
      (D ((m, k), true)).subtype (· ≠ p)).card = 4
    rw [subtype_ne_inter_card (hthrough _) (hthrough _)]
    dsimp only [D]
    rw [fourPointGlobalBlock_opposite_inter E T S hop,
      markedRow_card_five T (S m) hcard hdis (hs m)]
  let M : IntersectionFourMatching (link C p) 4 := {
    block := B ∘ e
    injective := hb_inj.comp e.injective
    mem := fun i => hb_mem (e i)
    inter := fun i => hb_inter (fourMatchingIndex i).1 (fourMatchingIndex i).2 }
  refine ⟨M, ?_⟩
  intro H hH
  have hHB (i : (Fin 2 × Fin 2) × Bool) : H ⊆ B i := by
    have hh := hH (e.symm i)
    simpa only [M, Function.comp_apply, Equiv.apply_symm_apply] using hh
  have hsubset : H ⊆ (T 0 \ {S 0 0}).subtype (· ≠ p) := by
    intro x hx
    apply mem_subtype.mpr
    have hd (i : (Fin 2 × Fin 2) × Bool) : x.val ∈ D i :=
      mem_subtype.mp (hHB i hx)
    have hxrow (k : Fin 2) : x.val ∈ markedRow T (S 0) k.succ := by
      have hh : x.val ∈ fourPointGlobalBlock E T S ((0, k), false) ∩
          fourPointGlobalBlock E T S ((0, k), true) := mem_inter.mpr ⟨hd _, hd _⟩
      rwa [fourPointGlobalBlock_opposite_inter E T S hop] at hh
    rw [← markedRow_one_inter_two T (S 0) hdis (hs 0)]
    exact mem_inter.mpr ⟨hxrow 0, hxrow 1⟩
  have hbound : ((T 0 \ {S 0 0}).subtype (· ≠ p)).card = 1 := by
    have hp' : p ∈ T 0 \ {S 0 0} := by simp [hp, Ne.symm (hsp 0)]
    rw [card_subtype, filter_ne', card_erase_of_mem hp',
      card_sdiff_of_subset (singleton_subset_iff.mpr (hs 0 0)), hcard]
    simp
  exact (card_le_card hsubset).trans_eq hbound

/-- Four independent intersection-four pairs whose endpoints have common
intersection of size at most one violate both GPPT geometric alternatives. -/
theorem four_pair_geometry_obstruction {D : Family α}
    (M : IntersectionFourMatching D 4)
    (hcommon : ∀ H : Finset α, (∀ i, H ⊆ M.block i) → H.card ≤ 1)
    (hgeometry : Nonempty (OrdinaryGeometry D) ∨ Nonempty (ExceptionalGeometry D)) :
    False := by
  rcases hgeometry with ho | he
  · obtain ⟨G⟩ := ho
    have hh := G.matching_le_three M
    omega
  · obtain ⟨G⟩ := he
    have hh := hcommon G.high (G.matching_subset M)
    rw [G.high_card] at hh
    omega

#guard_standard_axioms markedRow_card_five markedRow_injective markedRow_one_inter_two
  fourPointGlobalBlock_injective
  exists_four_point_matching four_pair_geometry_obstruction
  canonicalEdge_injective canonicalEdge_opposite_disjoint canonicalEdge_disjoint_triads

end CoveringDesigns.C13Structural
