import CoveringDesigns.C11_5_2.Geometry.Basic

/-!
The selected points in a Stanton trace frame are intrinsic. A marked trace
has a singleton intersection with its own triad and a two-point intersection
with either other triad. Even if the short trace has the same size profile,
it contains the selected point. This lets two endpoint descriptions of one
pair star be identified without choosing an isomorphism between nested links.
-/

namespace CoveringDesigns.C13Structural

open Finset StantonGeometry

variable {α : Type*} [DecidableEq α]

/-- Intersecting a marked trace with its distinguished triad recovers exactly
its selected point. -/
theorem markedRow_inter_self_triad (T : Fin 3 → Finset α) (s : Fin 3 → α)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hs : ∀ j, s j ∈ T j) (i : Fin 3) :
    markedRow T s i ∩ T i = {s i} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxrow, hxT⟩ := mem_inter.mp hx
    rcases mem_union.mp hxrow with hx | hx
    · exact hx
    · obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hx
      exact False.elim (disjoint_left.mp (hdis (mem_erase.mp hj).1)
        (mem_sdiff.mp hxj).1 hxT)
  · intro hx
    obtain rfl := mem_singleton.mp hx
    exact mem_inter.mpr ⟨mem_union_left _ (mem_singleton_self _), hs i⟩

/-- Intersecting a marked trace with another triad recovers its two
unselected points. -/
theorem markedRow_inter_other_triad (T : Fin 3 → Finset α) (s : Fin 3 → α)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hs : ∀ j, s j ∈ T j) {i j : Fin 3} (hij : i ≠ j) :
    markedRow T s i ∩ T j = T j \ {s j} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxrow, hxT⟩ := mem_inter.mp hx
    rcases mem_union.mp hxrow with hx | hx
    · obtain rfl := mem_singleton.mp hx
      exact False.elim (disjoint_left.mp (hdis hij) (hs i) hxT)
    · obtain ⟨k, hk, hxk⟩ := mem_biUnion.mp hx
      have hkj : k = j := by
        by_contra hne
        exact disjoint_left.mp (hdis hne) (mem_sdiff.mp hxk).1 hxT
      simpa only [hkj] using hxk
  · intro hx
    refine mem_inter.mpr ⟨mem_union_right _ ?_, (mem_sdiff.mp hx).1⟩
    exact mem_biUnion.mpr ⟨j, mem_erase.mpr ⟨hij.symm, mem_univ _⟩, hx⟩

/-- A singleton intersection of a residual Stanton trace with a triad can
only consist of that triad's selected point. -/
theorem selected_mem_of_trace_inter_singleton
    (T : Fin 3 → Finset α) (s : Fin 3 → α) (U : Finset α)
    (hcard : ∀ j, (T j).card = 3)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hs : ∀ j, s j ∈ T j) (hU : ∀ j, s j ∈ U)
    {B : Finset α} (hB : B ∈ insert U (univ.image (markedRow T s)))
    {j : Fin 3} {x : α} (hinter : B ∩ T j = {x}) : s j = x := by
  rcases mem_insert.mp hB with hB | hB
  · subst B
    have hm : s j ∈ U ∩ T j := mem_inter.mpr ⟨hU j, hs j⟩
    rw [hinter] at hm
    exact mem_singleton.mp hm
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hB
    by_cases hij : i = j
    · subst i
      rw [markedRow_inter_self_triad T s hdis hs] at hinter
      exact singleton_injective hinter
    · have he := markedRow_inter_other_triad T s hdis hs hij
      rw [he] at hinter
      have hc : (T j \ {s j}).card = 2 := by
        rw [card_sdiff_of_subset (singleton_subset_iff.mpr (hs j)), hcard]
        simp
      have hh := congrArg Finset.card hinter
      rw [hc, card_singleton] at hh
      omega

/-- Two descriptions of the same residual four-row family have exactly the
same selected point in every triad. The short traces need only contain all
three selected points; no further condition on their additions is used. -/
theorem selected_eq_of_rows_eq
    (T : Fin 3 → Finset α) (s t : Fin 3 → α) (U V : Finset α)
    (hcard : ∀ j, (T j).card = 3)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hs : ∀ j, s j ∈ T j) (ht : ∀ j, t j ∈ T j)
    (_hU : ∀ j, s j ∈ U) (hV : ∀ j, t j ∈ V)
    (hrows : insert U (univ.image (markedRow T s)) =
      insert V (univ.image (markedRow T t))) : s = t := by
  funext j
  have hm : markedRow T s j ∈ insert V (univ.image (markedRow T t)) := by
    rw [← hrows]
    exact mem_insert_of_mem (mem_image.mpr ⟨j, mem_univ _, rfl⟩)
  exact (selected_mem_of_trace_inter_singleton T t V hcard hdis ht hV hm
    (markedRow_inter_self_triad T s hdis hs j)).symm

/-- After the triads are aligned, the actual Stanton marking-frame API also
identifies selected points directly by its intrinsic short-point predicate. -/
theorem stanton_selected_eq_of_triad_eq [Fintype α]
    {C : Family α} {K L : Finset α} (F : MarkingFrame C K) (G : MarkingFrame C L)
    {i j : Fin 3} (hT : F.triads i = G.triads j) : F.selected i = G.selected j := by
  have hshort := (F.selected_iff _).mp (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  obtain ⟨k, _, he⟩ := mem_image.mp ((G.selected_iff _).mpr hshort)
  have hmem : F.selected i ∈ G.triads j := hT ▸ F.selected_mem i
  have hkj : k = j := by
    by_contra hne
    exact disjoint_left.mp (G.triads_disjoint hne) (G.selected_mem k) (he ▸ hmem)
  simpa only [hkj] using he.symm

#guard_standard_axioms markedRow_inter_self_triad markedRow_inter_other_triad
  selected_mem_of_trace_inter_singleton selected_eq_of_rows_eq
  stanton_selected_eq_of_triad_eq

end CoveringDesigns.C13Structural
