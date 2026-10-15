import CoveringDesigns.C12_6_3.Structural.CommonShort
import CoveringDesigns.C12_6_3.Structural.Moments
import CoveringDesigns.C12_6_3.GPPTConsequences

/-! GPPT Lemma 5.2: distinct minimum points have pair degree three.
The proof uses the two aligned Stanton frames, the six excess incidences,
and the intersection constraints of a third minimum star. -/

namespace CoveringDesigns.GPPTStructural

open Finset StantonGeometry

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace MinimumPairs

variable {C : Family α} {p q : α} {K : Finset α}

/-- Within a triad, a complementary row contains its selected point exactly
in that triad's own row, and the two other points in the other two rows. -/
theorem mem_markedRow_iff (F : RootedFrame C p K) {x : α} {i j : Fin 3}
    (hx : x ∈ F.triad j) :
    x ∈ markedRow F.triad F.selected i ↔
      (j = i ∧ x = F.selected j) ∨ (j ≠ i ∧ x ≠ F.selected j) := by
  have hindex {k : Fin 3} (hk : x ∈ F.triad k) : k = j := by
    by_contra hn
    exact disjoint_left.mp (F.pairwise_disjoint hn) hk hx
  constructor
  · intro hm
    rcases mem_union.mp hm with hs | hm
    · have hs : x = F.selected i := mem_singleton.mp hs
      have hi : i = j := hindex (hs ▸ F.selected_mem i)
      exact Or.inl ⟨hi.symm, hi ▸ hs⟩
    · obtain ⟨k, hk, hxt⟩ := mem_biUnion.mp hm
      have hk' := hindex (mem_sdiff.mp hxt).1
      subst k
      exact Or.inr ⟨(mem_erase.mp hk).1, by simpa using (mem_sdiff.mp hxt).2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hji, hxs⟩)
    · exact mem_union_left _ (mem_singleton_self _)
    · exact mem_union_right _ (mem_biUnion.mpr
        ⟨j, mem_erase.mpr ⟨hji, mem_univ _⟩, mem_sdiff.mpr ⟨hx, by simpa using hxs⟩⟩)

theorem row_not_mem_root (F : RootedFrame C p K) {x : α}
    (hx : x ∈ insert p K) (i : Fin 3) : x ∉ markedRow F.triad F.selected i := by
  intro hm
  rcases mem_union.mp hm with hs | hm
  · exact F.selected_not_mem_root i ((mem_singleton.mp hs) ▸ hx)
  · obtain ⟨j, _, hj⟩ := mem_biUnion.mp hm
    exact disjoint_left.mp (F.disjoint_root j) hx (mem_sdiff.mp hj).1

theorem row_mem (F : RootedFrame C p K) (i : Fin 3) :
    insert p (markedRow F.triad F.selected i) ∈ C := by
  apply (mem_filter.mp (show insert p (markedRow F.triad F.selected i) ∈ star C p from ?_)).1
  rw [F.star_eq]
  exact mem_insert_of_mem (mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩))

theorem row_injective (F : RootedFrame C p K) :
    Function.Injective (fun i => insert p (markedRow F.triad F.selected i)) := by
  intro i j he
  dsimp only at he
  have hi : F.selected i ∈ insert p (markedRow F.triad F.selected i) := by
    simp [markedRow]
  rw [he] at hi
  have hn : F.selected i ≠ p := by
    intro h
    exact F.selected_not_mem_root i (mem_insert.mpr (Or.inl h))
  have hm := (mem_markedRow_iff F (F.selected_mem i)).mp
    ((mem_insert.mp hi).resolve_left hn)
  simpa only [and_true, ne_eq, not_true_eq_false, and_false, or_false] using hm

/-- Six nonminimum points use all the available places outside the at least
six minimum points. Every other point is therefore minimum. -/
theorem minimum_outside_six (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hb : C.card ≤ 15) {S : Finset α} (hs : S.card = 6)
    (hS : ∀ x ∈ S, degree C x ≠ 7) {x : α} (hx : x ∉ S) : degree C x = 7 := by
  let N := univ.filter (fun y => degree C y ≠ 7)
  have hN : N.card ≤ 6 := by
    have hmin := six_minimum_points_at_most_fifteen hn hC hb
    have hc := card_filter_add_card_filter_not (s := (univ : Finset α))
      (p := fun y => degree C y = 7)
    change (minimumPoints C 7).card + N.card = (univ : Finset α).card at hc
    rw [card_univ, hn] at hc
    omega
  have hSN : S ⊆ N := by
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _, hS y hy⟩
  have he : S = N := eq_of_subset_of_card_le hSN (by omega)
  by_contra hd
  apply hx
  rw [he]
  exact mem_filter.mpr ⟨mem_univ _, hd⟩


theorem selected_injective (F : RootedFrame C p K) : Function.Injective F.selected := by
  intro i j he
  by_contra hij
  exact disjoint_left.mp (F.pairwise_disjoint hij) (F.selected_mem i)
    (he ▸ F.selected_mem j)

/-- In two aligned frames the shared short block leaves room for at most four
selected points, forcing agreement in at least two of the three triads. -/
theorem two_shared_selections {r : α}
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (ht : ∀ i, G.triad i = F.triad i)
    (hW : insert p F.shortTrace = insert q G.shortTrace) :
    2 ≤ (univ.filter (fun i => F.selected i = G.selected i)).card := by
  let A := univ.image F.selected
  let B := univ.image G.selected
  let I := univ.filter (fun i => F.selected i = G.selected i)
  have hA : A.card = 3 := by
    rw [card_image_of_injective _ (selected_injective F)]
    rfl
  have hB : B.card = 3 := by
    rw [card_image_of_injective _ (selected_injective G)]
    rfl
  have hI : I.image F.selected = A ∩ B := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact mem_inter.mpr ⟨mem_image.mpr ⟨i, mem_univ _, rfl⟩,
        mem_image.mpr ⟨i, mem_univ _, (mem_filter.mp hi).2.symm⟩⟩
    · intro hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp (mem_inter.mp hx).1
      obtain ⟨j, _, hj⟩ := mem_image.mp (mem_inter.mp hx).2
      have he : j = i := by
        by_contra hji
        have hm : G.selected j ∈ F.triad j := ht j ▸ G.selected_mem j
        exact disjoint_left.mp (F.pairwise_disjoint hji) hm (hj ▸ F.selected_mem i)
      subst j
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hj.symm⟩, rfl⟩
  have hcI : I.card = (A ∩ B).card := by
    rw [← hI, card_image_of_injective _ (selected_injective F)]
  have hqW : q ∈ F.shortTrace := by
    have hq : q ∈ insert p F.shortTrace := hW.symm ▸ mem_insert_self q G.shortTrace
    rcases mem_insert.mp hq with h | h
    · exact False.elim (F.root_not_mem_couple (by simp [← h]))
    · exact h
  have hsub : A ∪ B ⊆ F.shortTrace.erase q := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      refine mem_erase.mpr ⟨?_, F.selected_subset (mem_image.mpr ⟨i, mem_univ _, rfl⟩)⟩
      intro h
      exact F.selected_not_mem_root i (by simp [h])
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      have hn := G.selected_not_mem_root i
      have hw : G.selected i ∈ insert p F.shortTrace := hW.symm ▸
        mem_insert_of_mem (G.selected_subset (mem_image.mpr ⟨i, mem_univ _, rfl⟩))
      refine mem_erase.mpr ⟨?_, ?_⟩
      · intro h
        exact hn (by simp [h])
      · exact (mem_insert.mp hw).resolve_left (fun h => hn (by simp [h]))
  have hc := card_le_card hsub
  rw [card_erase_of_mem hqW, F.shortTrace_card] at hc
  have hu := card_union_add_card_inter A B
  change 2 ≤ I.card
  omega


/-- A shared triad places its two nonselected points together in both full
stars. These five distinct blocks force pair degree at least five. -/
theorem nonselected_pair_at_least_five {r x y : α}
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (ht : ∀ i, G.triad i = F.triad i) {j : Fin 3}
    (hs : F.selected j = G.selected j)
    (hx : x ∈ F.triad j) (hy : y ∈ F.triad j)
    (hxs : x ≠ F.selected j) (hys : y ≠ F.selected j) :
    5 ≤ degree (star C x) y := by
  let A := (univ.erase j).image (fun i => insert p (markedRow F.triad F.selected i))
  let B := (univ.erase j).image (fun i => insert q (markedRow G.triad G.selected i))
  let D := insert p ({q, r} ∪ F.triad j)
  have hqp : q ≠ p := by
    intro he
    exact F.root_not_mem_couple (by simp [he])
  have hA : A.card = 2 := by
    rw [card_image_of_injective _ (row_injective F)]
    simp
  have hB : B.card = 2 := by
    rw [card_image_of_injective _ (row_injective G)]
    simp
  have hnoq {E : Finset α} (hE : E ∈ A) : q ∉ E := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp hE
    simpa only [mem_insert, not_or] using ⟨hqp, row_not_mem_root F (by simp) i⟩
  have hnop {E : Finset α} (hE : E ∈ B) : p ∉ E := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp hE
    simpa only [mem_insert, not_or] using ⟨hqp.symm, row_not_mem_root G (by simp) i⟩
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    intro E hEA hEB
    obtain ⟨i, _, rfl⟩ := mem_image.mp hEA
    exact hnop hEB (mem_insert_self _ _)
  have hD : D ∉ A ∪ B := by
    intro h
    rcases mem_union.mp h with h | h
    · exact hnoq h (by simp [D])
    · exact hnop h (by simp [D])
  have hc : (insert D (A ∪ B)).card = 5 := by
    rw [card_insert_of_notMem hD, card_union_of_disjoint hdis, hA, hB]
  have hsub : insert D (A ∪ B) ⊆ star (star C x) y := by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact mem_filter.mpr ⟨mem_filter.mpr ⟨F.marked_mem j,
        mem_insert_of_mem (mem_union_right _ hx)⟩,
        mem_insert_of_mem (mem_union_right _ hy)⟩
    · rcases mem_union.mp hE with hE | hE
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp hE
        have hji : j ≠ i := (mem_erase.mp hi).1.symm
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨row_mem F i,
          mem_insert_of_mem ((mem_markedRow_iff F hx).mpr (Or.inr ⟨hji, hxs⟩))⟩,
          mem_insert_of_mem ((mem_markedRow_iff F hy).mpr (Or.inr ⟨hji, hys⟩))⟩
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp hE
        have hji : j ≠ i := (mem_erase.mp hi).1.symm
        have hx' : x ∈ G.triad j := (ht j).symm ▸ hx
        have hy' : y ∈ G.triad j := (ht j).symm ▸ hy
        have hxs' : x ≠ G.selected j := hs ▸ hxs
        have hys' : y ≠ G.selected j := hs ▸ hys
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨row_mem G i,
          mem_insert_of_mem ((mem_markedRow_iff G hx').mpr (Or.inr ⟨hji, hxs'⟩))⟩,
          mem_insert_of_mem ((mem_markedRow_iff G hy').mpr (Or.inr ⟨hji, hys'⟩))⟩
  have hh := card_le_card hsub
  change (insert D (A ∪ B)).card ≤ degree (star C x) y at hh
  omega

/-- Each of the two nonselected points in a shared triad is nonminimum. -/
theorem nonselected_nonminimum {r x : α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (ht : ∀ i, G.triad i = F.triad i) {j : Fin 3}
    (hs : F.selected j = G.selected j)
    (hx : x ∈ F.triad j) (hxs : x ≠ F.selected j) : degree C x ≠ 7 := by
  have hc : ((F.triad j).erase (F.selected j)).card = 2 := by
    rw [card_erase_of_mem (F.selected_mem j), F.triad_card]
  have hx' : x ∈ (F.triad j).erase (F.selected j) := mem_erase.mpr ⟨hxs, hx⟩
  have hc' : (((F.triad j).erase (F.selected j)).erase x).card = 1 := by
    rw [card_erase_of_mem hx', hc]
  obtain ⟨y, hy⟩ := card_pos.mp (by omega : 0 < (((F.triad j).erase (F.selected j)).erase x).card)
  obtain ⟨hyx, hy⟩ := mem_erase.mp hy
  obtain ⟨hys, hy⟩ := mem_erase.mp hy
  intro hd
  have hlo := nonselected_pair_at_least_five F G ht hs hx hy hxs hys
  have hhi := minimum_pair_degree_le_four hn hC hd hyx
  omega


theorem fin_three_exhaust {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (l : Fin 3) : l = i ∨ l = j ∨ l = k := by
  have he : ({i, j, k} : Finset (Fin 3)) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simp [hij, hik, hjk]
  have hm : l ∈ ({i, j, k} : Finset (Fin 3)) := by rw [he]; exact mem_univ _
  simpa only [mem_insert, mem_singleton] using hm

/-- If the third triad has the two distinct selections and one remaining
point, opposite full rows miss the residual triad of a new marking couple. -/
theorem opposite_rows_disjoint {r z : α}
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (ht : ∀ i, G.triad i = F.triad i) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : F.selected i = G.selected i) (hj : F.selected j = G.selected j)
    (hk : F.triad k = {F.selected k, G.selected k, z}) :
    Disjoint (insert q (markedRow G.triad G.selected j))
      (insert p (markedRow F.triad F.selected i) \ {p, G.selected k, z}) := by
  apply disjoint_left.mpr
  intro x hxG hxF
  obtain ⟨hxF, hxR⟩ := mem_sdiff.mp hxF
  have hxp : x ≠ p := fun h => hxR (by simp [h])
  have hxt : x ≠ G.selected k := fun h => hxR (by simp [h])
  have hxz : x ≠ z := fun h => hxR (by simp [h])
  have hxF := (mem_insert.mp hxF).resolve_left hxp
  have hxq : x ≠ q := by
    intro he
    exact row_not_mem_root F (by simp : q ∈ insert p ({q, r} : Finset α)) i (he ▸ hxF)
  have hxG := (mem_insert.mp hxG).resolve_left hxq
  have htriad : ∃ l, x ∈ F.triad l := by
    rcases mem_union.mp hxF with h | h
    · exact ⟨i, (mem_singleton.mp h) ▸ F.selected_mem i⟩
    · obtain ⟨l, _, hl⟩ := mem_biUnion.mp h
      exact ⟨l, (mem_sdiff.mp hl).1⟩
  obtain ⟨l, hl⟩ := htriad
  have hlG : x ∈ G.triad l := (ht l).symm ▸ hl
  have hf := (mem_markedRow_iff F hl).mp hxF
  have hg := (mem_markedRow_iff G hlG).mp hxG
  rcases fin_three_exhaust hij hik hjk l with hlI | hlJ | hlK
  · subst l
    have hxi : x = F.selected i := by simpa using hf
    have hni : x ≠ G.selected i := by simpa [hij] using hg
    exact hni (hxi.trans hi)
  · subst l
    have hxj : x = G.selected j := by simpa using hg
    have hnj : x ≠ F.selected j := by simpa [hij.symm] using hf
    exact hnj (hxj.trans hj.symm)
  · subst l
    rw [hk] at hl
    simp only [mem_insert, mem_singleton] at hl
    have hxs : x = F.selected k := hl.resolve_right (fun h => h.elim hxt hxz)
    rcases hf with ⟨hki, _⟩ | ⟨_, h⟩
    · exact hik hki.symm
    · exact h hxs

/-- A shared selected point occurs with the two roots in exactly the marked
block of its triad and the common short block. -/
theorem selected_triple_count (F : RootedFrame C p K) {q : α}
    (hqK : q ∈ K) (hqW : q ∈ F.shortTrace) (j : Fin 3) :
    containmentCount C {p, q, F.selected j} = 2 := by
  let W := insert p F.shortTrace
  let M := insert p (K ∪ F.triad j)
  have hneq : W ≠ M := F.short_ne_marked j
  have he : C.filter ({p, q, F.selected j} ⊆ ·) = {W, M} := by
    ext D
    constructor
    · intro hD
      obtain ⟨hDC, hD⟩ := mem_filter.mp hD
      have hpD := hD (by simp : p ∈ ({p, q, F.selected j} : Finset α))
      have hqD := hD (by simp : q ∈ ({p, q, F.selected j} : Finset α))
      have hsD := hD (by simp : F.selected j ∈ ({p, q, F.selected j} : Finset α))
      rcases CommonShort.member_with_couple F hqK hDC hpD hqD with h | ⟨i, hi⟩
      · exact mem_insert.mpr (Or.inl h)
      · have hsi : F.selected j ∈ F.triad i := by
          rw [hi] at hsD
          simp only [mem_insert, mem_union] at hsD
          rcases hsD with hs | hs | hs
          · exact False.elim (F.selected_not_mem_root j (mem_insert.mpr (Or.inl hs)))
          · exact False.elim (F.selected_not_mem_root j (mem_insert_of_mem hs))
          · exact hs
        have hij : i = j := by
          by_contra hn
          exact disjoint_left.mp (F.pairwise_disjoint hn) hsi (F.selected_mem j)
        subst i
        exact mem_insert.mpr (Or.inr (mem_singleton.mpr hi))
    · intro hD
      rcases mem_insert.mp hD with rfl | hD
      · refine mem_filter.mpr ⟨F.short_mem, ?_⟩
        simp only [insert_subset_iff, singleton_subset_iff]
        exact ⟨mem_insert_self _ _, mem_insert_of_mem hqW,
          mem_insert_of_mem (F.selected_subset (mem_image.mpr ⟨j, mem_univ _, rfl⟩))⟩
      · have hD : D = M := mem_singleton.mp hD
        subst D
        refine mem_filter.mpr ⟨F.marked_mem j, ?_⟩
        simp only [insert_subset_iff, singleton_subset_iff]
        exact ⟨mem_insert_self _ _, mem_insert_of_mem (mem_union_left _ hqK),
          mem_insert_of_mem (mem_union_right _ (F.selected_mem j))⟩
  unfold containmentCount
  rw [he]
  simp [hneq]

/-- A duplicate triple in a minimum link cannot have both remaining points
of pair degree three (GPPT Property 3.21). -/
theorem triple_two_forces_nonminimum {x : α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hpq : p ≠ q)
    (hxp : x ≠ p) (hxq : x ≠ q)
    (hpx : degree (star C p) x = 3) (hqx : degree (star C q) x = 3)
    (htriple : containmentCount C {p, q, x} = 2) : degree C x ≠ 7 := by
  intro hd
  let p' : {y : α // y ≠ x} := ⟨p, hxp.symm⟩
  let q' : {y : α // y ≠ x} := ⟨q, hxq.symm⟩
  have hpq' : p' ≠ q' := fun h => hpq (congrArg Subtype.val h)
  have hf := geometry_facts (by rw [complement_point_card, hn])
    (link_isCover hC x) (by rw [link_card, hd])
  have hp' : degree (link C x) p' = 3 := by
    rw [degree_link, pair_degree_comm]
    exact hpx
  have hq' : degree (link C x) q' = 3 := by
    rw [degree_link, pair_degree_comm]
    exact hqx
  have hm : multiplicity (link C x) {p', q'} = 2 := by
    have he := congrArg Finset.card (commonBlocks_liftBlock C x {p', q'})
    rw [card_image_of_injective _ (liftBlock_injective x)] at he
    have hl : liftBlock x {p', q'} = ({p, q, x} : Finset α) := by
      ext y
      simp [liftBlock, p', q', or_comm, or_left_comm]
    rw [hl] at he
    exact he.trans htriple
  rcases hf.multiplicity_two_free p' q' hpq' hm with h | h <;> omega

/-- The selected point of a shared triad is nonminimum as well. -/
theorem selected_nonminimum {r : α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (hqW : q ∈ F.shortTrace) {j : Fin 3}
    (hs : F.selected j = G.selected j) : degree C (F.selected j) ≠ 7 := by
  have hnp := F.selected_not_mem_root j
  have hpq : p ≠ q := fun he => F.root_not_mem_couple (by simp [he])
  have hxp : F.selected j ≠ p := fun he => hnp (by simp [he])
  have hxq : F.selected j ≠ q := fun he => hnp (by simp [he])
  apply triple_two_forces_nonminimum hn hC hpq hxp hxq
  · exact F.selected_pair_degree_three j
  · rw [hs]
    exact G.selected_pair_degree_three j
  · exact selected_triple_count F (by simp) hqW j


/-- Every point of a triad with matching selections is nonminimum. -/
theorem shared_triad_nonminimum {r : α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (ht : ∀ i, G.triad i = F.triad i) (hqW : q ∈ F.shortTrace) {j : Fin 3}
    (hs : F.selected j = G.selected j) {x : α} (hx : x ∈ F.triad j) :
    degree C x ≠ 7 := by
  by_cases he : x = F.selected j
  · rw [he]
    exact selected_nonminimum hn hC F G hqW hs
  · exact nonselected_nonminimum hn hC F G ht hs hx he

/-- Two shared triads exhaust the nonminimum points. The third triad consists
of minimum points, and its selections must differ. -/
theorem third_triad_minimum {r : α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15)
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (ht : ∀ i, G.triad i = F.triad i)
    (hW : insert p F.shortTrace = insert q G.shortTrace)
    (hdegree : degree (star C p) q = 4) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      F.selected i = G.selected i ∧ F.selected j = G.selected j ∧
      F.selected k ≠ G.selected k ∧ ∀ x ∈ F.triad k, degree C x = 7 := by
  have hqW := CommonShort.couple_mem_short_of_four F (by simp : q ∈ ({q, r} : Finset α)) hdegree
  obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq (two_shared_selections F G ht hW)
  obtain ⟨i, j, hij, heS⟩ := card_eq_two.mp hSc
  have hi : F.selected i = G.selected i :=
    (mem_filter.mp (hS (by rw [heS]; simp))).2
  have hj : F.selected j = G.selected j :=
    (mem_filter.mp (hS (by rw [heS]; simp))).2
  have hkcard : ((univ : Finset (Fin 3)) \ {i, j}).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ _)]
    simp [hij]
  obtain ⟨k, hk⟩ := card_pos.mp (by omega : 0 < ((univ : Finset (Fin 3)) \ {i, j}).card)
  have hik : i ≠ k := by
    intro he
    exact (mem_sdiff.mp hk).2 (by simp [he])
  have hjk : j ≠ k := by
    intro he
    exact (mem_sdiff.mp hk).2 (by simp [he])
  have hsix : (F.triad i ∪ F.triad j).card = 6 := by
    rw [card_union_of_disjoint (F.pairwise_disjoint hij), F.triad_card, F.triad_card]
  have hnon : ∀ x ∈ F.triad i ∪ F.triad j, degree C x ≠ 7 := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact shared_triad_nonminimum hn hC F G ht hqW hi hx
    · exact shared_triad_nonminimum hn hC F G ht hqW hj hx
  have hmin : ∀ x ∈ F.triad k, degree C x = 7 := by
    intro x hx
    apply minimum_outside_six hn hC hb hsix hnon
    intro hm
    rcases mem_union.mp hm with hm | hm
    · exact disjoint_left.mp (F.pairwise_disjoint hik) hm hx
    · exact disjoint_left.mp (F.pairwise_disjoint hjk) hm hx
  refine ⟨i, j, k, hij, hik, hjk, hi, hj, ?_, hmin⟩
  intro he
  exact selected_nonminimum hn hC F G hqW he (hmin _ (F.selected_mem k))

/-- When one triad has different selections, the common short trace is full:
it consists of the other root, the first three selections, and the new one. -/
theorem shortTrace_of_different_selection {r : α}
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (ht : ∀ i, G.triad i = F.triad i)
    (hW : insert p F.shortTrace = insert q G.shortTrace)
    {k : Fin 3} (hk : F.selected k ≠ G.selected k) :
    F.shortTrace = insert q (insert (G.selected k) (univ.image F.selected)) := by
  have hqW : q ∈ F.shortTrace := by
    have h := hW.symm ▸ mem_insert_self q G.shortTrace
    exact (mem_insert.mp h).resolve_left
      (fun he => F.root_not_mem_couple (by simp [he]))
  have htW : G.selected k ∈ F.shortTrace := by
    have h : G.selected k ∈ insert p F.shortTrace := hW.symm ▸
      mem_insert_of_mem (G.selected_subset (mem_image.mpr ⟨k, mem_univ _, rfl⟩))
    exact (mem_insert.mp h).resolve_left
      (fun he => G.selected_not_mem_root k (by simp [he]))
  have htS : G.selected k ∉ univ.image F.selected := by
    intro hm
    obtain ⟨l, _, hl⟩ := mem_image.mp hm
    have he : l = k := by
      by_contra hn
      exact disjoint_left.mp (F.pairwise_disjoint hn) (F.selected_mem l)
        (hl.symm ▸ (ht k ▸ G.selected_mem k))
    subst l
    exact hk hl
  have hqS : q ∉ insert (G.selected k) (univ.image F.selected) := by
    intro hm
    rcases mem_insert.mp hm with he | hm
    · exact G.selected_not_mem_root k (by simp [← he])
    · obtain ⟨l, _, hl⟩ := mem_image.mp hm
      exact F.selected_not_mem_root l (by simp [hl])
  symm
  apply eq_of_subset_of_card_le
  · exact insert_subset_iff.mpr ⟨hqW, insert_subset_iff.mpr ⟨htW, F.selected_subset⟩⟩
  · rw [F.shortTrace_card, card_insert_of_notMem hqS, card_insert_of_notMem htS,
      card_image_of_injective _ (selected_injective F)]
    decide

/-- A point outside the short block cannot have degree four in the link. -/
theorem nonshort_pair_degree_three (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (hp : degree C p = 7) (F : RootedFrame C p K) {x : α}
    (hxp : x ≠ p) (hxW : x ∉ F.shortTrace) : degree (star C p) x = 3 := by
  have hlo := pair_degree_at_least_three_12_6_3 hn hC hxp
  have hhi := minimum_pair_degree_le_four hn hC hp hxp
  have hfour : degree (star C p) x ≠ 4 := by
    intro hd
    let x' : {y : α // y ≠ p} := ⟨x, hxp⟩
    let W := F.shortTrace.subtype (· ≠ p)
    have hs : IsShortBlock (link C p) W :=
      (F.short_iff W).mpr (map_subtype_of_notMem p F.shortTrace F.root_not_mem_shortTrace)
    have hf := geometry_facts (by rw [complement_point_card, hn])
      (link_isCover hC p) (by rw [link_card, hp])
    have hd' : degree (link C p) x' = 4 := by rw [degree_link]; exact hd
    have hh := hf.free_in_short x' hd' W hs.1 hs
    exact hxW (mem_subtype.mp hh)
  omega


/-- The third minimum triad is impossible: in its remaining point's link,
a forced nonmarked block misses a marked triad entirely. -/
theorem minimum_third_triad_impossible {r : α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hp : degree C p = 7)
    (F : RootedFrame C p {q, r}) (G : RootedFrame C q {p, r})
    (ht : ∀ i, G.triad i = F.triad i)
    (hW : insert p F.shortTrace = insert q G.shortTrace) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : F.selected i = G.selected i) (hj : F.selected j = G.selected j)
    (hk : F.selected k ≠ G.selected k)
    (hmin : ∀ x ∈ F.triad k, degree C x = 7) : False := by
  let t := G.selected k
  have htT : t ∈ F.triad k := ht k ▸ G.selected_mem k
  have hts : t ≠ F.selected k := hk.symm
  have htE : t ∈ (F.triad k).erase (F.selected k) := mem_erase.mpr ⟨hts, htT⟩
  have hcard : (((F.triad k).erase (F.selected k)).erase t).card = 1 := by
    rw [card_erase_of_mem htE, card_erase_of_mem (F.selected_mem k), F.triad_card]
  obtain ⟨z, hz⟩ := card_pos.mp (by omega :
    0 < (((F.triad k).erase (F.selected k)).erase t).card)
  obtain ⟨hzt, hz⟩ := mem_erase.mp hz
  obtain ⟨hzs, hzT⟩ := mem_erase.mp hz
  have hT : F.triad k = {F.selected k, G.selected k, z} := by
    symm
    apply eq_of_subset_of_card_le
    · simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨F.selected_mem k, htT, hzT⟩
    · rw [F.triad_card]
      change 3 ≤ ({F.selected k, t, z} : Finset α).card
      simp [hts.symm, hzs.symm, hzt.symm]
  have hzroot : z ∉ insert p ({q, r} : Finset α) := by
    intro h
    exact disjoint_left.mp (F.disjoint_root k) h hzT
  have hzp : z ≠ p := fun he => hzroot (by simp [he])
  have hzq : z ≠ q := fun he => hzroot (by simp [he])
  have hpq : p ≠ q := fun he => F.root_not_mem_couple (by simp [he])
  have htp : t ≠ p := by
    intro he
    apply G.selected_not_mem_root k
    change t ∈ insert q ({p, r} : Finset α)
    simp [he]
  have hzW : z ∉ F.shortTrace := by
    rw [shortTrace_of_different_selection F G ht hW hk]
    intro hm
    rcases mem_insert.mp hm with he | hm
    · exact hzq he
    rcases mem_insert.mp hm with he | hm
    · exact hzt he
    obtain ⟨l, _, hl⟩ := mem_image.mp hm
    have hlk : l = k := by
      by_contra hne
      exact disjoint_left.mp (F.pairwise_disjoint hne) (F.selected_mem l) (hl.symm ▸ hzT)
    subst l
    exact hzs hl.symm
  have hpz : degree (star C p) z = 3 := nonshort_pair_degree_three hn hC hp F hzp hzW
  have hz7 : degree C z = 7 := hmin z hzT
  let M := insert p ({q, r} ∪ F.triad k)
  let R := fun l => insert p (markedRow F.triad F.selected l)
  have hnoq (l : Fin 3) : q ∉ R l := by
    simp only [R, mem_insert, not_or]
    exact ⟨hpq.symm, row_not_mem_root F (by simp) l⟩
  have hMR (l : Fin 3) : M ≠ R l := by
    intro he
    exact hnoq l (he ▸ (by simp [M] : q ∈ M))
  have hRR : R i ≠ R j := fun he => hij (row_injective F he)
  have hzR {l : Fin 3} (hkl : k ≠ l) : z ∈ R l :=
    mem_insert_of_mem ((mem_markedRow_iff F hzT).mpr (Or.inr ⟨hkl, hzs⟩))
  have htR {l : Fin 3} (hkl : k ≠ l) : t ∈ R l :=
    mem_insert_of_mem ((mem_markedRow_iff F htT).mpr (Or.inr ⟨hkl, hts⟩))
  have hmC : M ∈ commonBlocks C {z, p, t} := by
    refine mem_filter.mpr ⟨F.marked_mem k, ?_⟩
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨mem_insert_of_mem (mem_union_right _ hzT), mem_insert_self _ _,
      mem_insert_of_mem (mem_union_right _ htT)⟩
  have hrC {l : Fin 3} (hkl : k ≠ l) : R l ∈ commonBlocks C {z, p, t} := by
    refine mem_filter.mpr ⟨row_mem F l, ?_⟩
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hzR hkl, mem_insert_self _ _, htR hkl⟩
  have hthree : 3 ≤ (commonBlocks C {z, p, t}).card := by
    have hsub : ({M, R i, R j} : Family α) ⊆ commonBlocks C {z, p, t} := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hmC, hrC hik.symm, hrC hjk.symm⟩
    have hh := card_le_card hsub
    have hc : ({M, R i, R j} : Family α).card = 3 := by simp [hMR, hRR]
    omega
  obtain ⟨H⟩ := exists_rooted_frame hn hC hz7
    (by simp [hzp, hzt] : z ∉ ({p, t} : Finset α))
    (by simp [htp.symm] : ({p, t} : Finset α).card = 2) hthree
  have hpHW : p ∉ H.shortTrace :=
    H.couple_point_not_mem_short (by simp) (by rw [pair_degree_comm]; exact hpz)
  have hmarked : ∃ l, R i = insert z ({p, t} ∪ H.triad l) := by
    rcases CommonShort.member_with_couple H (by simp : p ∈ ({p, t} : Finset α))
      (row_mem F i) (hzR hik.symm) (mem_insert_self _ _) with he | hm
    · have hm : p ∈ insert z H.shortTrace := he ▸ mem_insert_self p (markedRow F.triad F.selected i)
      exact False.elim (hpHW ((mem_insert.mp hm).resolve_left hzp.symm))
    · exact hm
  obtain ⟨l, hl⟩ := hmarked
  have hroot : insert z ({p, t} : Finset α) = {p, G.selected k, z} := by
    ext x
    simp [t, or_comm, or_left_comm]
  have htriad : H.triad l = R i \ {p, G.selected k, z} := by
    have hh := congrArg (fun B => B \ insert z ({p, t} : Finset α)) hl
    rw [show insert z ({p, t} ∪ H.triad l) = insert z ({p, t} : Finset α) ∪ H.triad l from
      (insert_union z {p, t} (H.triad l)).symm] at hh
    rw [H.toRootTriads.marked_sdiff] at hh
    exact hh.symm.trans (congrArg (fun A => R i \ A) hroot)
  let B := insert q (markedRow G.triad G.selected j)
  have hzB : z ∈ B := mem_insert_of_mem ((mem_markedRow_iff G ((ht k).symm ▸ hzT)).mpr
    (Or.inr ⟨hjk.symm, hzt⟩))
  have hpB : p ∉ B := by
    simp only [B, mem_insert, not_or]
    exact ⟨hpq, row_not_mem_root G (by simp) j⟩
  obtain ⟨x, hx⟩ := H.nonmarked_meets_triad (row_mem G j) hzB
    (fun h => hpB (h (by simp : p ∈ ({p, t} : Finset α)))) l
  obtain ⟨hxB, hxT⟩ := mem_inter.mp hx
  rw [htriad] at hxT
  exact disjoint_left.mp (opposite_rows_disjoint F G ht hij hik hjk hi hj hT) hxB hxT

/-- Aligned pair-degree-four stars cannot fit in a cover with at most fifteen
blocks. All exclusion steps are structural. -/
theorem common_short_impossible
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15)
    (hp : degree C p = 7) (H : CommonShortFrame C p q)
    (hdegree : degree (star C p) q = 4) : False := by
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hmin⟩ :=
    third_triad_minimum hn hC hb H.first H.second H.triad_eq H.short_eq hdegree
  exact minimum_third_triad_impossible hn hC hp H.first H.second H.triad_eq H.short_eq
    hij hik hjk hi hj hk hmin

end MinimumPairs

/-- GPPT Lemma 5.2: two different degree-seven points have pair degree three. -/
theorem minimum_pair_degree_three {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15)
    {p q : α} (hp : degree C p = 7) (hq : degree C q = 7) (hpq : p ≠ q) :
    degree (star C p) q = 3 := by
  have hlo := pair_degree_at_least_three_12_6_3 hn hC hpq.symm
  have hhi := minimum_pair_degree_le_four hn hC hp hpq.symm
  have hfour : degree (star C p) q ≠ 4 := by
    intro hd
    obtain ⟨H⟩ := exists_common_short_frame hn hC hp hq hpq hd
    exact MinimumPairs.common_short_impossible hn hC hb hp H hd
  omega

#guard_standard_axioms MinimumPairs.nonselected_pair_at_least_five
  MinimumPairs.two_shared_selections MinimumPairs.triple_two_forces_nonminimum
  MinimumPairs.third_triad_minimum MinimumPairs.minimum_third_triad_impossible
  MinimumPairs.common_short_impossible minimum_pair_degree_three


end CoveringDesigns.GPPTStructural
