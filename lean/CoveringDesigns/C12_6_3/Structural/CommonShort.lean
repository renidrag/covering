import CoveringDesigns.C12_6_3.Structural.Frames

/-!
Two degree-seven points with pair degree four share a Stanton marking frame.
The construction is derived from the actual stars of the covering; the common
triads and common short block are conclusions, not normalization assumptions.
-/

namespace CoveringDesigns.GPPTStructural

open Finset StantonGeometry

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The common coordinates of the two minimum stars used in GPPT Lemma 5.2. -/
structure CommonShortFrame (C : Family α) (p q : α) where
  spouse : α
  first : RootedFrame C p {q, spouse}
  second : RootedFrame C q {p, spouse}
  triad_eq : ∀ i, second.triad i = first.triad i
  short_eq : insert p first.shortTrace = insert q second.shortTrace

namespace CommonShort

variable {C : Family α} {p q r : α} {K : Finset α}

private theorem couple_not_mem_row (F : RootedFrame C p K) {x : α}
    (hx : x ∈ K) (i : Fin 3) : x ∉ markedRow F.triad F.selected i := by
  intro hm
  rcases mem_union.mp hm with hs | hm
  · have he : x = F.selected i := mem_singleton.mp hs
    exact F.selected_not_mem_root i (mem_insert_of_mem (he ▸ hx))
  · obtain ⟨j, _, hj⟩ := mem_biUnion.mp hm
    exact disjoint_left.mp (F.disjoint_root j) (mem_insert_of_mem hx)
      (mem_sdiff.mp hj).1

theorem member_with_couple (F : RootedFrame C p K)
    {x : α} (hx : x ∈ K) {B : Finset α}
    (hB : B ∈ C) (hpB : p ∈ B) (hxB : x ∈ B) :
    B = insert p F.shortTrace ∨ ∃ j, B = insert p (K ∪ F.triad j) := by
  have hb : B ∈ star C p := mem_filter.mpr ⟨hB, hpB⟩
  rw [F.star_eq] at hb
  rcases mem_insert.mp hb with he | hb
  · exact Or.inl he
  · rcases mem_union.mp hb with hb | hb
    · obtain ⟨j, _, he⟩ := mem_image.mp hb
      exact Or.inr ⟨j, he.symm⟩
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hb
      rcases mem_insert.mp hxB with he | hm
      · exact False.elim (F.root_not_mem_couple (he ▸ hx))
      · exact False.elim (couple_not_mem_row F hx j hm)

private theorem marked_inter (F : RootedFrame C p K) {i j : Fin 3} (hij : i ≠ j) :
    insert p (K ∪ F.triad i) ∩ insert p (K ∪ F.triad j) = insert p K := by
  ext x
  have hd := disjoint_left.mp (F.pairwise_disjoint hij)
  simp only [mem_inter, mem_insert, mem_union]
  tauto

private theorem marked_ne (F : RootedFrame C p K) {i j : Fin 3} (hij : i ≠ j) :
    insert p (K ∪ F.triad i) ≠ insert p (K ∪ F.triad j) := by
  intro he
  apply hij
  apply F.toRootTriads.marked_injective
  simpa only [insert_union] using he

private theorem marked_not_other_short
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (i : Fin 3) : insert p ({q, r} ∪ F.triad i) ≠ insert q G.shortTrace := by
  intro he
  obtain ⟨j, hji⟩ := exists_ne i
  let D := insert p ({q, r} ∪ F.triad j)
  have hD : D ∈ C := F.marked_mem j
  have hqD : q ∈ D := by simp [D]
  have hpD : p ∈ D := mem_insert_self _ _
  rcases member_with_couple G (by simp : p ∈ ({p, r} : Finset α)) hD hqD hpD with hs | hm
  · exact marked_ne F hji (hs.trans he.symm)
  · obtain ⟨k, hk⟩ := hm
    have hs : G.selected k ∈ insert q G.shortTrace :=
      mem_insert_of_mem (G.selected_subset (mem_image.mpr ⟨k, mem_univ _, rfl⟩))
    have hm : G.selected k ∈ D := by
      rw [hk]
      exact mem_insert_of_mem (mem_union_right _ (G.selected_mem k))
    have hi : G.selected k ∈ insert p ({q, r} ∪ F.triad i) := he.symm ▸ hs
    have hr : G.selected k ∈ insert p ({q, r} : Finset α) := by
      rw [← marked_inter F hji]
      exact mem_inter.mpr ⟨hm, hi⟩
    apply G.selected_not_mem_root k
    simpa only [mem_insert, mem_singleton, or_left_comm] using hr

private theorem triads_match
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r}) :
    ∃ e : Equiv.Perm (Fin 3), ∀ i, G.triad (e i) = F.triad i := by
  classical
  have hmatch : ∀ i, ∃ j, G.triad j = F.triad i := by
    intro i
    have hm := member_with_couple G (by simp : p ∈ ({p, r} : Finset α))
      (F.marked_mem i) (by simp) (by simp)
    rcases hm with hs | ⟨j, hj⟩
    · exact False.elim (marked_not_other_short F G i hs)
    · refine ⟨j, ?_⟩
      have h := congrArg (fun B => B \ insert p ({q, r} : Finset α)) hj
      have hF := F.toRootTriads.marked_sdiff i
      have hG := G.toRootTriads.marked_sdiff j
      have hroot : insert p ({q, r} : Finset α) = insert q {p, r} := by
        ext x
        simp only [mem_insert, mem_singleton, or_left_comm]
      have hf : insert p ({q, r} ∪ F.triad i) \ insert p ({q, r} : Finset α) =
          F.triad i := by simpa only [insert_union] using hF
      have hg : insert q ({p, r} ∪ G.triad j) \ insert q ({p, r} : Finset α) =
          G.triad j := by simpa only [insert_union] using hG
      rw [hf] at h
      have hd := congrArg (fun A => insert q ({p, r} ∪ G.triad j) \ A) hroot
      exact hg.symm.trans (hd.symm.trans h.symm)
  choose e he using hmatch
  have hinj : Function.Injective e := by
    intro i j hij
    apply F.toRootTriads.triad_injective
    rw [← he i, ← he j, hij]
  exact ⟨Equiv.ofBijective e ⟨hinj, Finite.surjective_of_injective hinj⟩, he⟩

theorem couple_mem_short_of_four (F : RootedFrame C p K) {x : α}
    (hx : x ∈ K) (hdegree : degree (star C p) x = 4) : x ∈ F.shortTrace := by
  by_contra hn
  let M : Family α := univ.image (fun j => insert p (K ∪ F.triad j))
  have hsub : star (star C p) x ⊆ M := by
    intro B hB
    obtain ⟨hBp, hxB⟩ := mem_filter.mp hB
    obtain ⟨hBC, hpB⟩ := mem_filter.mp hBp
    rcases member_with_couple F hx hBC hpB hxB with hs | ⟨j, hj⟩
    · rw [hs] at hxB
      rcases mem_insert.mp hxB with he | hm
      · exact False.elim (F.root_not_mem_couple (he ▸ hx))
      · exact False.elim (hn hm)
    · exact mem_image.mpr ⟨j, mem_univ _, hj.symm⟩
  have hc : M.card = 3 := by
    simpa only [M, insert_union] using F.toRootTriads.marked_card
  have hh := card_le_card hsub
  change degree (star C p) x ≤ M.card at hh
  omega

/-- Once the marking couples share their spouse, the common coordinates follow
from the star equations and pair degree four. -/
theorem of_frames (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (_hpq : p ≠ q) (hdegree : degree (star C p) q = 4) :
    Nonempty (CommonShortFrame C p q) := by
  obtain ⟨e, he⟩ := triads_match F G
  let G' := G.reindex e
  have ht (i : Fin 3) : G'.triad i = F.triad i := he i
  have hqW : q ∈ F.shortTrace := couple_mem_short_of_four F (by simp) hdegree
  have hw := member_with_couple G' (by simp : p ∈ ({p, r} : Finset α))
    F.short_mem (mem_insert_of_mem hqW) (mem_insert_self _ _)
  have hshort : insert p F.shortTrace = insert q G'.shortTrace := by
    rcases hw with hs | ⟨j, hj⟩
    · exact hs
    · apply False.elim
      apply F.short_ne_marked j
      rw [ht j] at hj
      simpa only [insert_union, insert_comm] using hj
  exact ⟨⟨r, F, G', ht, hshort⟩⟩

/-- An actual couple in the first link provides both marking frames. The second
couple is forced by the same three common blocks of the original covering. -/
theorem of_link_spouse (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hp : degree C p = 7) (hq : degree C q = 7) (hpq : p ≠ q)
    (hdegree : degree (star C p) q = 4)
    (r : {x : α // x ≠ p})
    (hspouse : IsCouple (link C p) {⟨q, hpq.symm⟩, r}) :
    Nonempty (CommonShortFrame C p q) := by
  let q' : {x : α // x ≠ p} := ⟨q, hpq.symm⟩
  have hqr : q ≠ r.val := by
    intro he
    have hh : q' = r := Subtype.ext he
    have hc := hspouse.1
    change ({q', r} : Finset {x : α // x ≠ p}).card = 2 at hc
    simp [hh] at hc
  have hpr : p ≠ r.val := r.property.symm
  have hc := congrArg Finset.card (commonBlocks_liftBlock C p {q', r})
  rw [card_image_of_injective _ (liftBlock_injective p)] at hc
  have he : liftBlock p {q', r} = ({p, q, r.val} : Finset α) := by
    simp [liftBlock, q']
  rw [he] at hc
  have htriple : 3 ≤ (commonBlocks C {p, q, r.val}).card := by
    rw [← hc]
    exact hspouse.2
  obtain ⟨F⟩ := exists_rooted_frame hn hC hp
    (by simp [hpq, hpr] : p ∉ ({q, r.val} : Finset α))
    (by simp [hqr] : ({q, r.val} : Finset α).card = 2) htriple
  have htriple' : 3 ≤ (commonBlocks C {q, p, r.val}).card := by
    simpa only [insert_comm] using htriple
  obtain ⟨G⟩ := exists_rooted_frame hn hC hq
    (by simp [hpq.symm, hqr] : q ∉ ({p, r.val} : Finset α))
    (by simp [hpr] : ({p, r.val} : Finset α).card = 2) htriple'
  exact of_frames F G hpq hdegree

end CommonShort

/-- The common-frame normalization is available for every hypothetical pair
of degree-seven points of pair degree four in a `(12,6,3)` covering. -/
theorem exists_common_short_frame {C : Family α} {p q : α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hp : degree C p = 7) (hq : degree C q = 7) (hpq : p ≠ q)
    (hdegree : degree (star C p) q = 4) :
    Nonempty (CommonShortFrame C p q) := by
  let q' : {x : α // x ≠ p} := ⟨q, hpq.symm⟩
  have hd : degree (link C p) q' = 4 := by
    rw [degree_link]
    exact hdegree
  obtain ⟨r, _, hspouse⟩ := degree_four_has_spouse
    (by rw [complement_point_card, hn]) (link_isCover hC p)
    (by rw [link_card, hp]) hd
  exact CommonShort.of_link_spouse hn hC hp hq hpq hdegree r hspouse

#guard_standard_axioms CommonShort.of_frames CommonShort.of_link_spouse
  exists_common_short_frame

end CoveringDesigns.GPPTStructural
