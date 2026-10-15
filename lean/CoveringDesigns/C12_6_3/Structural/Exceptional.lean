import CoveringDesigns.C12_6_3.Structural.Triplicate

/-!
The coordinate transport in GPPT Lemma 5.8, Case 2.  One triad has the same
selected point in all three rows; the other selection columns are injective.
The two companions of the common selected point are the only additions to
each short trace.  These structural facts give the fifteen blocks of Figure 6.
-/

set_option maxHeartbeats 1000000

namespace CoveringDesigns.GPPTStructural

open Finset

namespace TriplicateFrame

variable {α : Type*} [DecidableEq α] [Fintype α] {C : Family α}

private def exceptionalCode : Fin 3 ⊕ (Fin 3 × Fin 3) ≃ Fin 12 :=
  (Equiv.sumCongr (Equiv.refl (Fin 3)) finProdFinEquiv).trans finSumFinEquiv

private def exceptionalRoots : Finset (Fin 12) :=
  univ.image fun r : Fin 3 => exceptionalCode (.inl r)

private def exceptionalTriads (j : Fin 3) : Finset (Fin 12) :=
  univ.image fun r : Fin 3 => exceptionalCode (.inr (j, r))

private def exceptionalSelected (r j : Fin 3) : Fin 12 :=
  exceptionalCode (.inr (j, if j = 0 then 0 else r))

private def exceptionalShort (r : Fin 3) : Finset (Fin 12) :=
  univ.image (exceptionalSelected r) ∪
    (exceptionalTriads 0).erase (exceptionalCode (.inr (0, 0)))

private theorem figure6_formula : figure6 =
    (univ.image fun j => exceptionalRoots ∪ exceptionalTriads j) ∪
    (univ.biUnion fun r : Fin 3 => univ.image fun j =>
      insert (exceptionalCode (.inl r))
        (StantonGeometry.markedRow exceptionalTriads (exceptionalSelected r) j)) ∪
    (univ.image fun r => insert (exceptionalCode (.inl r)) (exceptionalShort r)) := by
  decide +kernel

omit [DecidableEq α] [Fintype α] in
private theorem exists_triad_enumeration (T : Finset α) (hT : T.card = 3)
    (x : α) (hx : x ∈ T) :
    ∃ f : Fin 3 → α, Function.Injective f ∧ (∀ r, f r ∈ T) ∧ f 0 = x := by
  let e : T ≃ Fin 3 := Finset.equivFinOfCardEq hT
  let p : Equiv.Perm (Fin 3) := Equiv.swap 0 (e ⟨x, hx⟩)
  refine ⟨fun r => (e.symm (p r)).val, ?_, ?_, ?_⟩
  · intro r s he
    exact p.injective (e.symm.injective (Subtype.ext he))
  · intro r
    exact (e.symm (p r)).property
  · simp [p]

private def exceptionalPointAt (F : TriplicateFrame C) (q : Fin 3 → Fin 3 → α) :
    Fin 3 ⊕ (Fin 3 × Fin 3) → α
  | .inl r => F.roots r
  | .inr (j, r) => q j r

private theorem exceptionalPointAt_injective (F : TriplicateFrame C)
    (σ : Equiv.Perm (Fin 3)) (q : Fin 3 → Fin 3 → α)
    (hq : ∀ j r, q j r ∈ F.common.triad (σ j))
    (hi : ∀ j, Function.Injective (q j)) :
    Function.Injective (exceptionalPointAt F q) := by
  intro a b he
  rcases a with r | ⟨j, r⟩ <;> rcases b with s | ⟨k, s⟩ <;>
    dsimp only [exceptionalPointAt] at he
  · exact congrArg Sum.inl (F.roots_injective he)
  · have hr : F.roots r ∈ univ.image F.roots := mem_image.mpr ⟨r, mem_univ _, rfl⟩
    exact (disjoint_left.mp (F.common.disjoint_root (σ k)) hr (he ▸ hq k s)).elim
  · have hs : F.roots s ∈ univ.image F.roots := mem_image.mpr ⟨s, mem_univ _, rfl⟩
    exact (disjoint_left.mp (F.common.disjoint_root (σ j)) hs (he ▸ hq j r)).elim
  · have hjk := σ.injective (F.triad_eq_of_mem (hq j r) (he ▸ hq k s))
    subst k
    have hrs := hi j he
    subst s
    rfl

private theorem exists_exceptional_coordinates (F : TriplicateFrame C)
    (hn : Fintype.card α = 12) (σ : Equiv.Perm (Fin 3))
    (q : Fin 3 → Fin 3 → α)
    (hq : ∀ j r, q j r ∈ F.common.triad (σ j))
    (hi : ∀ j, Function.Injective (q j)) :
    ∃ e : α ≃ Fin 12,
      (∀ r, e (F.roots r) = exceptionalCode (.inl r)) ∧
      (∀ j r, e (q j r) = exceptionalCode (.inr (j, r))) := by
  have hf := exceptionalPointAt_injective F σ q hq hi
  have hs : univ.image (exceptionalPointAt F q) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_image_of_injective _ hf]
    simp [hn]
  have hb : Function.Bijective (exceptionalPointAt F q) := by
    refine ⟨hf, fun x => ?_⟩
    have hx : x ∈ univ.image (exceptionalPointAt F q) := by
      rw [hs]
      exact mem_univ _
    obtain ⟨i, _, hi⟩ := mem_image.mp hx
    exact ⟨i, hi⟩
  let e := (Equiv.ofBijective (exceptionalPointAt F q) hb).symm.trans exceptionalCode
  have he (a : Fin 3 ⊕ (Fin 3 × Fin 3)) :
      e (exceptionalPointAt F q a) = exceptionalCode a :=
    congrArg exceptionalCode
      ((Equiv.ofBijective (exceptionalPointAt F q) hb).symm_apply_apply a)
  exact ⟨e, fun r => he (.inl r), fun j r => he (.inr (j, r))⟩

omit [Fintype α] in
private theorem exceptional_markedRow_map {β : Type*} [DecidableEq β]
    (e : α ≃ β) (T : Fin 3 → Finset α) (s : Fin 3 → α) (j : Fin 3) :
    (StantonGeometry.markedRow T s j).map e.toEmbedding =
      StantonGeometry.markedRow (fun k => (T k).map e.toEmbedding) (e ∘ s) j := by
  simp only [StantonGeometry.markedRow, map_eq_image, image_union, biUnion_image,
    image_sdiff _ _ e.toEmbedding.injective, image_singleton, Function.comp_def,
    Equiv.toEmbedding_apply]

private theorem relabel_eq_figure6_of_coordinates (F : TriplicateFrame C)
    (e : α ≃ Fin 12) (σ : Equiv.Perm (Fin 3))
    (hr : ∀ r, e (F.roots r) = exceptionalCode (.inl r))
    (ht : ∀ j, (F.common.triad (σ j)).map e.toEmbedding = exceptionalTriads j)
    (hs : ∀ r j, e ((F.row r).selected (σ j)) = exceptionalSelected r j)
    (hw : ∀ r, ((F.row r).shortTrace).map e.toEmbedding = exceptionalShort r) :
    relabel e C = figure6 := by
  have hroots : (univ.image F.roots).map e.toEmbedding = exceptionalRoots := by
    simp only [map_eq_image, image_image, Function.comp_def, exceptionalRoots]
    congr 1
    funext r
    exact hr r
  have hcommon : ((univ.image fun j => univ.image F.roots ∪ F.common.triad j).map
      (Finset.mapEmbedding e.toEmbedding).toEmbedding) =
        univ.image fun j => exceptionalRoots ∪ exceptionalTriads j := by
    rw [map_eq_image, image_image]
    change univ.image (fun j => (univ.image F.roots ∪ F.common.triad j).map
      e.toEmbedding) = _
    rw [← univ_image_perm σ]
    congr 1
    funext j
    rw [map_union, hroots, ht]
  have hfull : ((univ.biUnion fun r => univ.image fun j =>
      insert (F.roots r) (StantonGeometry.markedRow F.common.triad (F.row r).selected j)).map
      (Finset.mapEmbedding e.toEmbedding).toEmbedding) =
      univ.biUnion fun r : Fin 3 => univ.image fun j =>
        insert (exceptionalCode (.inl r))
          (StantonGeometry.markedRow exceptionalTriads (exceptionalSelected r) j) := by
    simp only [map_eq_image, biUnion_image, image_image, Function.comp_def]
    apply biUnion_congr rfl
    intro r _
    change univ.image (fun j => (insert (F.roots r)
      (StantonGeometry.markedRow F.common.triad (F.row r).selected j)).map
        e.toEmbedding) = _
    rw [← univ_image_perm σ]
    congr 1
    funext j
    rw [map_insert]
    simp only [Equiv.toEmbedding_apply]
    rw [hr, ← markedRow_reindex _ _ σ j, exceptional_markedRow_map]
    simp only [ht, Function.comp_def, hs]
  have hshort : ((univ.image fun r => insert (F.roots r) (F.row r).shortTrace).map
      (Finset.mapEmbedding e.toEmbedding).toEmbedding) =
        univ.image fun r => insert (exceptionalCode (.inl r)) (exceptionalShort r) := by
    rw [map_eq_image, image_image]
    congr 1
    funext r
    change (insert (F.roots r) (F.row r).shortTrace).map e.toEmbedding = _
    rw [map_insert, hw]
    simp only [Equiv.toEmbedding_apply, hr]
  unfold relabel
  conv_lhs => arg 2; rw [F.blocks_eq]
  rw [map_union, map_union, figure6_formula, hcommon, hfull, hshort]

/-- The fixed-shape transport in GPPT Case 2, stated independently of the
counting argument which forces the additions and the other two columns. -/
theorem common_column_isomorphic_figure6_of_injective (F : TriplicateFrame C)
    (hn : Fintype.card α = 12) {x : α} {j : Fin 3}
    (hx : x ∈ F.common.triad j) (hsel : ∀ r, (F.row r).selected j = x)
    (hadd : ∀ r, F.additions r = (F.common.triad j).erase x)
    (hi : ∀ k, k ≠ j → Function.Injective fun r => (F.row r).selected k) :
    Isomorphic C figure6 := by
  obtain ⟨f, hfi, hfm, hf0⟩ := exists_triad_enumeration (F.common.triad j)
    (F.common.triad_card j) x hx
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 j
  have hσ : σ 0 = j := by simp [σ]
  let q : Fin 3 → Fin 3 → α := fun k r => if k = 0 then f r else (F.row r).selected (σ k)
  have hqm (k r : Fin 3) : q k r ∈ F.common.triad (σ k) := by
    by_cases hk : k = 0
    · simpa [q, hk, hσ] using hfm r
    · simpa [q, hk] using (F.row r).selected_mem (σ k)
  have hqi (k : Fin 3) : Function.Injective (q k) := by
    by_cases hk : k = 0
    · simpa [q, hk] using hfi
    · have hkj : σ k ≠ j := fun he => hk (σ.injective (he.trans hσ.symm))
      simpa [q, hk] using hi (σ k) hkj
  obtain ⟨e, her, heq⟩ := exists_exceptional_coordinates F hn σ q hqm hqi
  have het (k : Fin 3) : (F.common.triad (σ k)).map e.toEmbedding = exceptionalTriads k := by
    have he : univ.image (q k) = F.common.triad (σ k) := by
      apply eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨r, _, rfl⟩ := mem_image.mp hy
        exact hqm k r
      · rw [card_image_of_injective _ (hqi k), F.common.triad_card]
        rfl
    rw [← he, map_eq_image, image_image]
    change univ.image (fun r => e (q k r)) = exceptionalTriads k
    simp only [heq, exceptionalTriads]
  have hes (r k : Fin 3) :
      e ((F.row r).selected (σ k)) = exceptionalSelected r k := by
    by_cases hk : k = 0
    · have he0 := heq 0 0
      simp only [q, ite_true, hf0] at he0
      simpa [hk, hσ, hsel, exceptionalSelected] using he0
    · simpa [q, hk, exceptionalSelected] using heq k r
  have hex : e x = exceptionalCode (.inr (0, 0)) := by
    simpa [q, hf0] using heq 0 0
  have hew (r : Fin 3) : ((F.row r).shortTrace).map e.toEmbedding = exceptionalShort r := by
    have hw : (F.row r).shortTrace =
        univ.image (F.row r).selected ∪ (F.common.triad j).erase x := by
      rw [← hadd r]
      exact (union_sdiff_of_subset (F.row r).selected_subset).symm
    have hselected : (univ.image (F.row r).selected).map e.toEmbedding =
        univ.image (exceptionalSelected r) := by
      rw [map_eq_image, image_image]
      change univ.image (fun k => e ((F.row r).selected k)) = _
      rw [← univ_image_perm σ]
      simp only [hes]
    rw [hw, map_union, hselected, map_erase]
    simp only [Equiv.toEmbedding_apply, hex]
    have ht0 := het 0
    rw [hσ] at ht0
    rw [ht0]
    rfl
  exact ⟨e, relabel_eq_figure6_of_coordinates F e σ her het hes hew⟩

/-- GPPT Lemma 5.8, Case 2: the common selected point forces the unique
exceptional covering, by short-trace saturation and the minimum-degree columns. -/
theorem common_column_isomorphic_figure6 (F : TriplicateFrame C)
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hc : C.card = 15)
    {x : α} {j : Fin 3} (hx : x ∈ F.common.triad j)
    (hsel : ∀ r, (F.row r).selected j = x) : Isomorphic C figure6 := by
  exact F.common_column_isomorphic_figure6_of_injective hn hx hsel
    (F.additions_eq_common_mates hn hC hx hsel)
    (fun _ hk => F.other_column_injective hn hC hc hx hsel hk)

#guard_standard_axioms common_column_isomorphic_figure6_of_injective
  common_column_isomorphic_figure6

end TriplicateFrame

end CoveringDesigns.GPPTStructural
