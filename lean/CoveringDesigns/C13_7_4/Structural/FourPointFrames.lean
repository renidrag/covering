import CoveringDesigns.C12_6_3.Structural.TriplicateClassification
import CoveringDesigns.C13_7_4.Structural.Basic

/-! Structural frames around four minimum points.  The prescribed-root
version of the GPPT frame existence theorem preserves the coordinates needed
to compare the four vertex links. -/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural StantonGeometry

set_option maxHeartbeats 1600000

variable {α : Type*} [DecidableEq α]

theorem exists_triplicate_frame_roots [Fintype α] {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15)
    (roots : Fin 3 → α) (hinj : Function.Injective roots)
    (hdegree : ∀ i, degree C (roots i) = 7)
    (hpair : ∀ i j, i ≠ j → degree (star C (roots i)) (roots j) = 3)
    (hthree : (commonBlocks C (univ.image roots)).card = 3) :
    ∃ F : TriplicateFrame C, F.roots = roots := by
  classical
  let A := univ.image roots
  have hmem (i : Fin 3) : roots i ∈ A := mem_image.mpr ⟨i, mem_univ _, rfl⟩
  have hroot (i : Fin 3) : insert (roots i) (A.erase (roots i)) = A :=
    insert_erase (hmem i)
  have hcard : A.card = 3 := by
    dsimp only [A]
    rw [card_image_of_injective _ hinj]
    rfl
  have hex (i : Fin 3) : Nonempty (RootedFrame C (roots i) (A.erase (roots i))) := by
    apply exists_rooted_frame hn hC (hdegree i) (notMem_erase _ _)
    · rw [card_erase_of_mem (hmem i), hcard]
    · rw [hroot]
      exact Nat.le_of_eq hthree.symm
  let F (i : Fin 3) := Classical.choice (hex i)
  let G : RootTriads A := (F 0).toRootTriads.cast (hroot 0)
  have hG (j : Fin 3) : G.triad j = (F 0).triad j :=
    (F 0).toRootTriads.cast_triad (hroot 0) j
  have hmarked (j : Fin 3) : A ∪ G.triad j ∈ C := by
    rw [hG]
    simpa only [← insert_union, hroot] using (F 0).marked_mem j
  have hrow (i : Fin 3) : ∃ R : AlignedRow C (roots i) G,
      R.shortTrace = (F i).shortTrace :=
    (F i).exists_alignedRow G (hroot i) hmarked hthree
  choose R hR using hrow
  have hshort (i : Fin 3) : Disjoint A (R i).shortTrace := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    rw [hR i] at hy
    by_cases hji : j = i
    · subst j
      exact (F i).root_not_mem_shortTrace hy
    · exact (F i).couple_point_not_mem_short
        (mem_erase.mpr ⟨fun he => hji (hinj he), hmem j⟩)
        (hpair i j (Ne.symm hji)) hy
  have himage : A = {roots 0, roots 1, roots 2} := by
    ext x
    simp [A, Fin.exists_fin_succ, eq_comm]
  have hcover : star C (roots 0) ∪ star C (roots 1) ∪ star C (roots 2) = C := by
    apply three_minimum_stars_cover C (roots 0) (roots 1) (roots 2) hb
      (hdegree 0) (hdegree 1) (hdegree 2)
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
    simpa only [← himage] using hthree
  have hcover' : univ.biUnion (fun r => star C (roots r)) = C := by
    convert hcover using 1
    ext B
    simp [Fin.exists_fin_succ]
  refine ⟨⟨roots, hinj, G, R, hdegree, hshort, ?_⟩, rfl⟩
  apply hcover'.symm.trans
  ext B
  simp only [mem_biUnion, mem_univ, true_and, (R _).star_eq,
    mem_insert, mem_union, mem_image]
  constructor
  · rintro ⟨r, h | h | h⟩
    · exact Or.inr ⟨r, h.symm⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨r, h⟩)
  · rintro ((h | ⟨r, h⟩) | ⟨r, h⟩)
    · exact ⟨0, Or.inr (Or.inl h)⟩
    · exact ⟨r, Or.inr (Or.inr h)⟩
    · exact ⟨r, Or.inl h.symm⟩

/-- A GPPT triplicate frame lifted from a minimum point link.  Its roots are
three further points of the original covering, so each private row is carried
by one edge of the four-point root set. -/
structure FourPointVertex [Fintype α] (C : Family α) (p : α) (K : Finset α) where
  neighbor : Fin 3 → α
  neighbor_injective : Function.Injective neighbor
  neighbor_ne : ∀ r, neighbor r ≠ p
  roots_eq : insert p (univ.image neighbor) = K
  common : RootTriads K
  selected : Fin 3 → Fin 3 → α
  selected_mem : ∀ r j, selected r j ∈ common.triad j
  short : Fin 3 → Finset α
  short_card : ∀ r, (short r).card = 5
  short_disjoint : ∀ r, Disjoint K (short r)
  selected_subset : ∀ r, univ.image (selected r) ⊆ short r
  pair_blocks : ∀ r, star (star C p) (neighbor r) =
    insert (insert p (insert (neighbor r) (short r)))
      ((univ.image fun j => K ∪ common.triad j) ∪
        (univ.image fun j => insert p (insert (neighbor r)
          (markedRow common.triad (selected r) j))))
  blocks_eq : star C p =
    (univ.image fun j => K ∪ common.triad j) ∪
    (univ.biUnion fun r => univ.image fun j =>
      insert p (insert (neighbor r) (markedRow common.triad (selected r) j))) ∪
    (univ.image fun r => insert p (insert (neighbor r) (short r)))
  column_pattern : ∀ j, Function.Injective (fun r => selected r j) ∨
    ∃ x, ∀ r, selected r j = x
  common_additions : ∀ j x, (∀ r, selected r j = x) →
    ∀ r, short r \ univ.image (selected r) = (common.triad j).erase x

private theorem markedRow_map_subtype (p : α)
    (T : Fin 3 → Finset {q : α // q ≠ p}) (s : Fin 3 → {q : α // q ≠ p})
    (i : Fin 3) :
    (markedRow T s i).map (Function.Embedding.subtype _) =
      markedRow (fun j => (T j).map (Function.Embedding.subtype _))
        (fun j => (s j).val) i := by
  simp only [markedRow, map_eq_image, Function.Embedding.coe_subtype, image_union, biUnion_image,
    image_sdiff _ _ Subtype.val_injective, image_singleton]

private theorem liftBlock_insert (p : α) (x : {q : α // q ≠ p})
    (B : Finset {q : α // q ≠ p}) :
    liftBlock p (insert x B) = insert p (insert x.val
      (B.map (Function.Embedding.subtype _))) := by
  simp [liftBlock]

private theorem liftBlock_union (p : α) (A B : Finset {q : α // q ≠ p}) :
    liftBlock p (A ∪ B) = liftBlock p A ∪ B.map (Function.Embedding.subtype _) := by
  simp only [liftBlock, map_union, insert_union]

private theorem image_map_subtype (p : α) (f : Fin 3 → {q : α // q ≠ p}) :
    (univ.image f).map (Function.Embedding.subtype _) =
      univ.image (fun i => (f i).val) := by
  simp only [map_eq_image, image_image, Function.comp_def, Function.Embedding.coe_subtype]

/-- Lifting does not alter selections, short traces or their incidences. -/
def FourPointVertex.ofTriplicate [Fintype α] {C : Family α} (p : α)
    (F : TriplicateFrame (link C p))
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hp : degree C p = 15) :
    FourPointVertex C p (insert p (univ.image fun r => (F.roots r).val)) := by
  let e : {q : α // q ≠ p} ↪ α := Function.Embedding.subtype _
  let K := insert p (univ.image fun r => (F.roots r).val)
  have hTunion : univ.biUnion F.common.triad = univ \ univ.image F.roots := by
    symm
    rw [← F.common.spans, union_sdiff_distrib]
    simp only [sdiff_self, bot_eq_empty, empty_union]
    exact sdiff_eq_self_of_disjoint ((disjoint_biUnion_left _ _ _).mpr
      (fun j _ => (F.common.disjoint_root j).symm))
  let G' := RootTriads.ofSubtype p (univ.image F.roots) F.common.triad
    F.common.triad_card F.common.pairwise_disjoint hTunion
  have hK : insert p ((univ.image F.roots).map e) = K := by
    simp only [image_map_subtype, K, e]
  let G : RootTriads K := G'.cast hK
  have hG (j : Fin 3) : G.triad j = (F.common.triad j).map e := by
    exact G'.cast_triad hK j
  have hhC : IsCover (link C p) 6 3 := link_isCover hC p
  have hhn : Fintype.card {q : α // q ≠ p} = 12 := by
    rw [complement_point_card, hn]
  have hhc : (link C p).card = 15 := by rw [link_card, hp]
  have hlift : liftBlock p (univ.image F.roots) = K := by
    simpa only [liftBlock] using hK
  have hcommon (j : Fin 3) : liftBlock p (univ.image F.roots ∪ F.common.triad j) =
      K ∪ G.triad j := by
    rw [liftBlock_union, hlift, hG]
  have hshort (r : Fin 3) : liftBlock p (insert (F.roots r) (F.row r).shortTrace) =
      insert p (insert (F.roots r).val ((F.row r).shortTrace.map e)) :=
    liftBlock_insert p _ _
  have hprivate (r j : Fin 3) :
      liftBlock p (insert (F.roots r) (markedRow F.common.triad (F.row r).selected j)) =
        insert p (insert (F.roots r).val (markedRow G.triad
          (fun i => ((F.row r).selected i).val) j)) := by
    rw [liftBlock_insert, markedRow_map_subtype]
    have hfun : G.triad = fun i => (F.common.triad i).map e := funext hG
    rw [hfun]
  refine ⟨(fun r => (F.roots r).val), ?_, (fun r => (F.roots r).property), rfl,
    G, (fun r j => ((F.row r).selected j).val), ?_,
    (fun r => (F.row r).shortTrace.map e), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r s he
    exact F.roots_injective (Subtype.ext he)
  · intro r j
    rw [hG]
    exact mem_map.mpr ⟨(F.row r).selected j, (F.row r).selected_mem j, rfl⟩
  · intro r
    simpa using (F.row r).shortTrace_card
  · intro r
    change Disjoint K ((F.row r).shortTrace.map e)
    rw [← hK, disjoint_insert_left]
    exact ⟨root_not_mem_map p _, (disjoint_map e).mpr (F.short_disjoint_roots r)⟩
  · intro r
    simpa only [e, image_map_subtype] using
      (map_subset_map.mpr (F.row r).selected_subset :
        (univ.image (F.row r).selected).map e ⊆ (F.row r).shortTrace.map e)
  · intro r
    have he := congrArg (fun D => D.image (liftBlock p)) (F.row r).star_eq
    rw [star_link, liftBlock_link] at he
    have hc : star (star C (F.roots r).val) p = star (star C p) (F.roots r).val := by
      ext B
      simp [star, and_comm, and_assoc]
    rw [hc] at he
    simpa only [image_insert, image_union, image_image, Function.comp_def,
      hshort, hcommon, hprivate] using he
  · have he := congrArg (fun D => D.image (liftBlock p)) F.blocks_eq
    rw [liftBlock_link] at he
    simpa only [image_union, image_image, biUnion_image, Function.comp_def,
      hshort, hcommon, hprivate] using he
  · intro j
    rcases F.columns_injective_or_common hhn hhC hhc with hi | ⟨k, x, hk⟩
    · exact Or.inl (Subtype.val_injective.comp (hi j))
    · by_cases hjk : j = k
      · subst k
        exact Or.inr ⟨x.val, fun r => congrArg Subtype.val (hk r)⟩
      · have hx : x ∈ F.common.triad k := hk 0 ▸ (F.row 0).selected_mem k
        exact Or.inl (Subtype.val_injective.comp
          (F.other_column_injective hhn hhC hhc hx hk hjk))
  · intro j x hx r
    have hxp : x ≠ p := by
      rw [← hx 0]
      exact ((F.row 0).selected j).property
    let y : {q : α // q ≠ p} := ⟨x, hxp⟩
    have hsel : ∀ r, (F.row r).selected j = y := fun r => Subtype.ext (hx r)
    have hy : y ∈ F.common.triad j := hsel 0 ▸ (F.row 0).selected_mem j
    have he := congrArg (Finset.map e) (F.additions_eq_common_mates hhn hhC hy hsel r)
    simpa only [TriplicateFrame.additions, map_sdiff, image_map_subtype, map_erase,
      hG, e, y, Function.Embedding.coe_subtype] using he

/-- Reordering the common triads does not change any of the global blocks. -/
def FourPointVertex.reindex [Fintype α] {C : Family α} {p : α} {K : Finset α}
    (F : FourPointVertex C p K) (σ : Equiv.Perm (Fin 3)) : FourPointVertex C p K where
  neighbor := F.neighbor
  neighbor_injective := F.neighbor_injective
  neighbor_ne := F.neighbor_ne
  roots_eq := F.roots_eq
  common := F.common.reindex σ
  selected r j := F.selected r (σ j)
  selected_mem r j := F.selected_mem r (σ j)
  short := F.short
  short_card := F.short_card
  short_disjoint := F.short_disjoint
  selected_subset r := by rw [univ_image_perm]; exact F.selected_subset r
  pair_blocks r := by
    simp only [RootTriads.reindex, markedRow_reindex]
    rw [univ_image_perm σ (fun j => K ∪ F.common.triad j),
      univ_image_perm σ (fun j => insert p (insert (F.neighbor r)
        (markedRow F.common.triad (F.selected r) j)))]
    exact F.pair_blocks r
  blocks_eq := by
    simp only [RootTriads.reindex, markedRow_reindex]
    rw [univ_image_perm σ (fun j => K ∪ F.common.triad j)]
    have hrows (r : Fin 3) :
        (univ.image fun j => insert p (insert (F.neighbor r)
          (markedRow F.common.triad (F.selected r) (σ j)))) =
        (univ.image fun j => insert p (insert (F.neighbor r)
          (markedRow F.common.triad (F.selected r) j))) :=
      univ_image_perm σ (fun j => insert p (insert (F.neighbor r)
        (markedRow F.common.triad (F.selected r) j)))
    simp only [hrows]
    exact F.blocks_eq
  column_pattern j := F.column_pattern (σ j)
  common_additions j x hx r := by
    rw [univ_image_perm]
    exact F.common_additions (σ j) x hx r

namespace FourPointVertex

variable [Fintype α] {C : Family α} {p : α} {K : Finset α}
  (F : FourPointVertex C p K)

include F in
theorem root_mem : p ∈ K := by
  simpa only [F.roots_eq] using (mem_insert_self p (univ.image F.neighbor))

theorem neighbor_mem (r : Fin 3) : F.neighbor r ∈ K := by
  have hm : F.neighbor r ∈ insert p (univ.image F.neighbor) :=
    mem_insert_of_mem (mem_image.mpr ⟨r, mem_univ _, rfl⟩)
  simpa only [F.roots_eq] using hm

theorem neighbor_surjective {q : α} (hq : q ∈ K) (hne : q ≠ p) :
    ∃ r, F.neighbor r = q := by
  rw [← F.roots_eq] at hq
  exact (by simpa using (mem_insert.mp hq).resolve_left hne)

theorem common_mem (j : Fin 3) : K ∪ F.common.triad j ∈ C := by
  have hm : K ∪ F.common.triad j ∈ star C p := by
    rw [F.blocks_eq]
    exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨j, mem_univ _, rfl⟩))
  exact (mem_filter.mp hm).1

theorem marked_mem (r j : Fin 3) :
    insert p (insert (F.neighbor r) (markedRow F.common.triad (F.selected r) j)) ∈ C := by
  have hm : insert p (insert (F.neighbor r)
      (markedRow F.common.triad (F.selected r) j)) ∈ star C p := by
    rw [F.blocks_eq]
    exact mem_union_left _ (mem_union_right _
      (mem_biUnion.mpr ⟨r, mem_univ _, mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩))
  exact (mem_filter.mp hm).1

include F in
/-- The three common blocks intrinsically align the triads of every vertex. -/
theorem exists_aligned (G : RootTriads K)
    (hG : ∀ j, K ∪ G.triad j ∈ C)
    (hthree : containmentCount C K = 3) :
    ∃ H : FourPointVertex C p K, H.common.triad = G.triad := by
  obtain ⟨σ, hσ⟩ := G.alignment F.common hG F.common_mem hthree
  exact ⟨F.reindex σ, funext hσ⟩

end FourPointVertex

/-- A bad quadruple supplies a triplicate GPPT frame at any of its roots. -/
theorem exists_fourPointVertex [Fintype α] {C : Family α} {K : Finset α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hK : K.card = 4)
    (hthree : containmentCount C K = 3) {p : α} (hpK : p ∈ K)
    (hp : degree C p = 15)
    (hpair : ∀ q ∈ K, q ≠ p → degree (star C p) q = 7) :
    Nonempty (FourPointVertex C p K) := by
  classical
  let J : Finset {q : α // q ≠ p} := K.subtype (· ≠ p)
  have hJ : J.card = 3 := by
    rw [card_subtype, filter_ne', card_erase_of_mem hpK, hK]
  let e : Fin 3 ≃ {q // q ∈ J} := (Fintype.equivFinOfCardEq
    (by rw [Fintype.card_coe, hJ] : Fintype.card {q // q ∈ J} = 3)).symm
  let roots : Fin 3 → {q : α // q ≠ p} := fun r => (e r).val
  have hi : Function.Injective roots := Subtype.val_injective.comp e.injective
  have hroots : univ.image roots = J := by
    change univ.image (Subtype.val ∘ e) = J
    rw [← image_image, image_univ_equiv]
    ext x
    simp
  have hJlift : liftBlock p J = K := liftBlock_subtype p hpK
  have hd (r : Fin 3) : degree (link C p) (roots r) = 7 := by
    rw [degree_link]
    exact hpair (roots r).val (mem_subtype.mp (e r).property) (roots r).property
  have hpairs (r s : Fin 3) (hrs : r ≠ s) :
      degree (star (link C p) (roots r)) (roots s) = 3 :=
    minimum_pair_degree_three (by rw [complement_point_card, hn])
      (link_isCover hC p) (by rw [link_card, hp]) (hd r) (hd s)
      (fun h => hrs (hi h))
  have hc : (commonBlocks (link C p) (univ.image roots)).card = 3 := by
    change containmentCount (link C p) (univ.image roots) = 3
    rw [hroots, containmentCount_link]
    change containmentCount C (liftBlock p J) = 3
    rwa [hJlift]
  obtain ⟨F, hF⟩ := exists_triplicate_frame_roots
    (by rw [complement_point_card, hn]) (link_isCover hC p)
    (by rw [link_card, hp]) roots hi hd hpairs hc
  have he : insert p (univ.image fun r => (F.roots r).val) = K := by
    rw [hF, ← image_map_subtype]
    rw [hroots]
    exact hJlift
  exact ⟨he ▸ FourPointVertex.ofTriplicate p F hn hC hp⟩

#guard_standard_axioms exists_triplicate_frame_roots FourPointVertex.ofTriplicate
  FourPointVertex.reindex FourPointVertex.exists_aligned exists_fourPointVertex

end CoveringDesigns.C13Structural
