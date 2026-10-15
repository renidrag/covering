import CoveringDesigns.C11_5_2.Geometry.Representatives
import CoveringDesigns.C11_5_2.Stanton

/-! The Fano plane on the seven rows of a Stanton covering.

The rigidity argument below is a general argument about triples.  If only two
old triples remain unrecorded, the three pairs of any proposed new triple must
belong to those two triples.  Two of the pairs therefore belong to the same old
triple, and force equality.  No labelled configurations are enumerated. -/

namespace CoveringDesigns.StantonGeometry

open Finset

variable {ρ σ : Type*} [DecidableEq ρ] [DecidableEq σ]

/-- Incidence axioms for the seven lines on the seven rows. -/
structure FanoPlane (F : Finset (Finset ρ)) : Prop where
  lines_card : F.card = 7
  line_card : ∀ L ∈ F, L.card = 3
  pair_exists : ∀ a b : ρ, a ≠ b → ∃ L ∈ F, a ∈ L ∧ b ∈ L
  pair_unique : ∀ L ∈ F, ∀ M ∈ F, ∀ a ∈ L, ∀ b ∈ L,
    a ≠ b → a ∈ M → b ∈ M → L = M
  line_meet : ∀ L ∈ F, ∀ M ∈ F, (L ∩ M).Nonempty

/-- Three pairs covered by two triples force the triangle to be one of them. -/
theorem triangle_of_two_triples {T L M : Finset ρ}
    (hT : T.card = 3) (hL : L.card = 3) (hM : M.card = 3)
    (hp : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      (a ∈ L ∧ b ∈ L) ∨ (a ∈ M ∧ b ∈ M)) : T = L ∨ T = M := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hT
  have ha : a ∈ ({a, b, c} : Finset ρ) := by simp
  have hb : b ∈ ({a, b, c} : Finset ρ) := by simp
  have hc : c ∈ ({a, b, c} : Finset ρ) := by simp
  have heq (N : Finset ρ) (hN : N.card = 3)
      (haN : a ∈ N) (hbN : b ∈ N) (hcN : c ∈ N) :
      ({a, b, c} : Finset ρ) = N := by
    apply eq_of_subset_of_card_le
    · simpa only [insert_subset_iff, singleton_subset_iff] using ⟨haN, hbN, hcN⟩
    · simpa [hab, hac, hbc] using hN.le
  rcases hp a ha b hb hab with habL | habM
  · rcases hp a ha c hc hac with hacL | hacM
    · exact Or.inl (heq L hL habL.1 habL.2 hacL.2)
    · rcases hp b hb c hc hbc with hbcL | hbcM
      · exact Or.inl (heq L hL habL.1 habL.2 hbcL.2)
      · exact Or.inr (heq M hM hacM.1 hbcM.1 hacM.2)
  · rcases hp a ha c hc hac with hacL | hacM
    · rcases hp b hb c hc hbc with hbcL | hbcM
      · exact Or.inl (heq L hL hacL.1 hbcL.1 hacL.2)
      · exact Or.inr (heq M hM habM.1 habM.2 hbcM.2)
    · exact Or.inr (heq M hM habM.1 habM.2 hacM.2)

private theorem triple_mem_of_two_missing {F G : Finset (Finset ρ)}
    (hF : FanoPlane F) (hG : FanoPlane G)
    {L M : Finset ρ} (hL : L ∈ F) (hM : M ∈ F)
    (hmissing : F \ G ⊆ {L, M}) : G ⊆ F := by
  intro T hT
  by_contra hTF
  have hp : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      (a ∈ L ∧ b ∈ L) ∨ (a ∈ M ∧ b ∈ M) := by
    intro a ha b hb hab
    obtain ⟨N, hNF, haN, hbN⟩ := hF.pair_exists a b hab
    have hNG : N ∉ G := by
      intro hNG
      exact hTF ((hG.pair_unique T hT N hNG a ha b hb hab haN hbN) ▸ hNF)
    have hNM := hmissing (mem_sdiff.mpr ⟨hNF, hNG⟩)
    simp only [mem_insert, mem_singleton] at hNM
    rcases hNM with rfl | rfl
    · exact Or.inl ⟨haN, hbN⟩
    · exact Or.inr ⟨haN, hbN⟩
  rcases triangle_of_two_triples (hG.line_card T hT)
      (hF.line_card L hL) (hF.line_card M hM) hp with rfl | rfl
  · exact hTF hL
  · exact hTF hM

/-- Five common lines determine the whole plane. -/
theorem FanoPlane.eq_of_five_common {F G : Finset (Finset ρ)}
    (hF : FanoPlane F) (hG : FanoPlane G) (hcommon : 5 ≤ (F ∩ G).card) :
    F = G := by
  have hsmall : (F \ G).card ≤ 2 := by
    have hsum := card_sdiff_add_card_inter F G
    rw [hF.lines_card] at hsum
    omega
  by_cases hzero : F \ G = ∅
  · have hsub : F ⊆ G := sdiff_eq_empty_iff_subset.mp hzero
    exact eq_of_subset_of_card_le hsub (by rw [hF.lines_card, hG.lines_card])
  obtain ⟨L, hLD⟩ := nonempty_iff_ne_empty.mpr hzero
  have hLF : L ∈ F := (mem_sdiff.mp hLD).1
  by_cases hone : (F \ G).erase L = ∅
  · have hmissing : F \ G ⊆ {L, L} := by
      intro M hM
      have he : M = L := by
        by_contra hn
        have hm := mem_erase.mpr ⟨hn, hM⟩
        rw [hone] at hm
        exact notMem_empty M hm
      simp [he]
    exact (eq_of_subset_of_card_le
      (triple_mem_of_two_missing hF hG hLF hLF hmissing)
      (by rw [hF.lines_card, hG.lines_card])).symm
  obtain ⟨M, hMD⟩ := nonempty_iff_ne_empty.mpr hone
  have hML : M ≠ L := (mem_erase.mp hMD).1
  have hMF : M ∈ F := (mem_sdiff.mp (mem_erase.mp hMD).2).1
  have hpair : ({L, M} : Finset (Finset ρ)) = F \ G := by
    apply eq_of_subset_of_card_le
    · simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hLD, (mem_erase.mp hMD).2⟩
    · simpa [Ne.symm hML] using hsmall
  exact (eq_of_subset_of_card_le
    (triple_mem_of_two_missing hF hG hLF hMF (by rw [← hpair]))
    (by rw [hF.lines_card, hG.lines_card])).symm

/-- Row relabelling preserves the Fano incidence axioms. -/
theorem FanoPlane.relabel {F : Finset (Finset ρ)} (hF : FanoPlane F) (e : ρ ≃ σ) :
    FanoPlane (CoveringDesigns.relabel e F) := by
  constructor
  · rw [relabel_card, hF.lines_card]
  · intro L hL
    obtain ⟨L, hLF, rfl⟩ := mem_map.mp hL
    simpa using hF.line_card L hLF
  · intro a b hab
    have hne : e.symm a ≠ e.symm b := by simpa only [ne_eq, e.symm.injective.eq_iff]
    obtain ⟨L, hL, ha, hb⟩ := hF.pair_exists (e.symm a) (e.symm b) hne
    exact ⟨L.map e.toEmbedding, (mem_relabel e F L).mpr hL,
      by simpa using ha, by simpa using hb⟩
  · intro L hL M hM a ha b hb hab haM hbM
    obtain ⟨L, hLF, rfl⟩ := mem_map.mp hL
    obtain ⟨M, hMF, rfl⟩ := mem_map.mp hM
    apply congrArg (fun N : Finset ρ => N.map e.toEmbedding)
    apply hF.pair_unique L hLF M hMF (e.symm a) (by simpa using ha)
      (e.symm b) (by simpa using hb)
    · simpa only [ne_eq, e.symm.injective.eq_iff] using hab
    · simpa using haM
    · simpa using hbM
  · intro L hL M hM
    obtain ⟨L, hLF, rfl⟩ := mem_map.mp hL
    obtain ⟨M, hMF, rfl⟩ := mem_map.mp hM
    obtain ⟨a, ha⟩ := hF.line_meet L hLF M hMF
    exact ⟨e a, by simpa using ha⟩

/-- A single labelled plane, used by both displayed Stanton representatives. -/
def fanoLines : Family (Fin 7) :=
  {{0, 2, 5}, {0, 3, 4}, {1, 2, 4}, {1, 3, 5},
   {0, 1, 6}, {2, 3, 6}, {4, 5, 6}}

/-- The row order exposes the same underlying Fano plane in both types. -/
def fanoRepresentativeRow (tag : Bool) : Fin 7 → Finset (Fin 11) :=
  if tag then
    ![{0, 1, 4, 5, 8}, {2, 3, 6, 7, 8}, {0, 2, 4, 6, 9},
      {1, 3, 5, 7, 9}, {1, 2, 5, 6, 10}, {0, 3, 4, 7, 10},
      {0, 4, 8, 9, 10}]
  else
    ![{0, 1, 2, 3, 4}, {2, 5, 6, 7, 8}, {0, 3, 5, 7, 9},
      {1, 3, 6, 8, 9}, {1, 4, 5, 7, 10}, {0, 4, 6, 8, 10},
      {2, 3, 4, 9, 10}]

section FixedFanoChecks
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype
set_option synthInstance.maxSize 2048

theorem fanoLines_plane : FanoPlane fanoLines := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro L hL M hM a ha b hb hab haM hbM
    have h : ∀ i j : Fin 7, ∀ L ∈ fanoLines, ∀ M ∈ fanoLines,
        i ≠ j → i ∈ L → j ∈ L → i ∈ M → j ∈ M → L = M := by
      decide +kernel
    exact h a b L hL M hM hab ha hb haM hbM
  · decide +kernel

theorem fanoRepresentativeRow_image (tag : Bool) :
    univ.image (fanoRepresentativeRow tag) = stantonRepresentative tag := by
  cases tag <;> decide +kernel

theorem fanoRepresentativeRow_injective (tag : Bool) :
    Function.Injective (fanoRepresentativeRow tag) := by
  unfold Function.Injective
  cases tag <;> decide +kernel

theorem fanoRepresentativeRow_columns (tag : Bool) :
    ∀ q : Fin 11, ∃ L ∈ fanoLines, ∀ i ∈ L, q ∈ fanoRepresentativeRow tag i := by
  cases tag <;> decide +kernel

end FixedFanoChecks

/-- The displayed seven row labels are an equivalence with the actual rows. -/
noncomputable def fanoRepresentativeRowEquiv (tag : Bool) :
    Fin 7 ≃ ↥(stantonRepresentative tag) :=
  Equiv.ofBijective
    (fun i => ⟨fanoRepresentativeRow tag i, by
      rw [← fanoRepresentativeRow_image tag]
      exact mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)
    ⟨by
      intro i j hij
      exact fanoRepresentativeRow_injective tag (congrArg Subtype.val hij), by
      intro B
      have hB : B.val ∈ univ.image (fanoRepresentativeRow tag) := by
        simpa only [fanoRepresentativeRow_image] using B.property
      obtain ⟨i, _, hi⟩ := mem_image.mp hB
      exact ⟨i, Subtype.ext hi⟩⟩

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A column regarded as a subset of the row type. -/
def incidentRows (C : Family α) (q : α) : Finset ↥C :=
  univ.filter fun B => q ∈ B.val

theorem incidentRows_card (C : Family α) (q : α) :
    (incidentRows C q).card = degree C q := by
  change (C.attach.filter fun B => q ∈ B.val).card = (C.filter fun B => q ∈ B).card
  rw [filter_attach (fun B : Finset α => q ∈ B) C, card_map, card_attach]

/-- The row equivalence induced by a relabelling of the points. -/
def fanoRowRelabel (e : α ≃ β) (C : Family α) : ↥C ≃ ↥(relabel e C) :=
  Equiv.subtypeEquiv (Equiv.finsetCongr e) (fun B => (mem_relabel e C B).symm)

/-- Every column contains one of the seven local projective lines. -/
def HasFanoColumns (C : Family α) : Prop :=
  ∃ F : Family ↥C, FanoPlane F ∧ ∀ q, ∃ L ∈ F, L ⊆ incidentRows C q

theorem representative_hasFanoColumns (tag : Bool) :
    HasFanoColumns (stantonRepresentative tag) := by
  let e := fanoRepresentativeRowEquiv tag
  refine ⟨relabel e fanoLines, fanoLines_plane.relabel e, ?_⟩
  intro q
  obtain ⟨L, hL, hq⟩ := fanoRepresentativeRow_columns tag q
  refine ⟨L.map e.toEmbedding, (mem_relabel e fanoLines L).mpr hL, ?_⟩
  intro B hB
  obtain ⟨i, hi, rfl⟩ := mem_map.mp hB
  exact mem_filter.mpr ⟨mem_univ _, hq i hi⟩

theorem HasFanoColumns.relabel {C : Family α} (hC : HasFanoColumns C) (e : α ≃ β) :
    HasFanoColumns (CoveringDesigns.relabel e C) := by
  obtain ⟨F, hF, hcol⟩ := hC
  let r := fanoRowRelabel e C
  refine ⟨CoveringDesigns.relabel r F, hF.relabel r, ?_⟩
  intro q
  obtain ⟨p, rfl⟩ := e.surjective q
  obtain ⟨L, hL, hp⟩ := hcol p
  refine ⟨L.map r.toEmbedding, (mem_relabel r F L).mpr hL, ?_⟩
  intro B hB
  obtain ⟨D, hD, rfl⟩ := mem_map.mp hB
  have hpD := (mem_filter.mp (hp hD)).2
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  change e p ∈ D.val.map e.toEmbedding
  simpa using hpD

/-- Structural Stanton classification supplies the local plane for every
seven-row covering on eleven points. -/
theorem exists_fano_columns [Fintype α] {C : Family α}
    (hn : Fintype.card α = 11) (hC : IsCover C 5 2) (hb : C.card = 7) :
    ∃ F : Family ↥C, FanoPlane F ∧ ∀ q, ∃ L ∈ F, L ⊆ incidentRows C q := by
  obtain ⟨tag, e, he⟩ := stanton_classification_on hn hC hb
  have h := (representative_hasFanoColumns tag).relabel e.symm
  rw [← he, relabel_symm_relabel] at h
  exact h

theorem fano_column_of_degree_three {C : Family α} {F : Family ↥C}
    (hF : FanoPlane F) (hcol : ∀ q, ∃ L ∈ F, L ⊆ incidentRows C q)
    {q : α} (hq : degree C q = 3) : incidentRows C q ∈ F := by
  obtain ⟨L, hL, hsub⟩ := hcol q
  have he : L = incidentRows C q := eq_of_subset_of_card_le hsub
    (by rw [incidentRows_card, hq, hF.line_card L hL])
  exact he ▸ hL

/-- Five distinct degree-three columns identify any proposed row geometry
with the plane furnished by Stanton. -/
theorem fano_eq_of_five_columns {C : Family α} {F G : Family ↥C}
    (hF : FanoPlane F) (hcol : ∀ q, ∃ L ∈ F, L ⊆ incidentRows C q)
    (hG : FanoPlane G) (I : Finset α) (hI : 5 ≤ I.card)
    (hdegree : ∀ q ∈ I, degree C q = 3)
    (hinj : Set.InjOn (incidentRows C) I)
    (hknown : ∀ q ∈ I, incidentRows C q ∈ G) : F = G := by
  apply hF.eq_of_five_common hG
  have hsub : I.image (incidentRows C) ⊆ F ∩ G := by
    intro L hL
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hL
    exact mem_inter.mpr
      ⟨fano_column_of_degree_three hF hcol (hdegree q hq), hknown q hq⟩
  have hc : (I.image (incidentRows C)).card = I.card := card_image_iff.mpr hinj
  exact hI.trans (hc ▸ card_le_card hsub)

/-- Once five degree-three columns fix the local Fano plane, no column can
omit a whole line. This is the precise local input for the projective proof. -/
theorem column_meets_line_of_five_columns [Fintype α] {C : Family α}
    (hn : Fintype.card α = 11) (hC : IsCover C 5 2) (hb : C.card = 7)
    {G : Family ↥C} (hG : FanoPlane G) (I : Finset α) (hI : 5 ≤ I.card)
    (hdegree : ∀ q ∈ I, degree C q = 3)
    (hinj : Set.InjOn (incidentRows C) I)
    (hknown : ∀ q ∈ I, incidentRows C q ∈ G)
    (q : α) {L : Finset ↥C} (hL : L ∈ G) :
    (L ∩ incidentRows C q).Nonempty := by
  obtain ⟨F, hF, hcol⟩ := exists_fano_columns hn hC hb
  have he := fano_eq_of_five_columns hF hcol hG I hI hdegree hinj hknown
  subst F
  obtain ⟨M, hM, hm⟩ := hcol q
  obtain ⟨B, hB⟩ := hG.line_meet L hL M hM
  exact ⟨B, mem_inter.mpr ⟨(mem_inter.mp hB).1, hm (mem_inter.mp hB).2⟩⟩

#guard_standard_axioms triangle_of_two_triples FanoPlane.eq_of_five_common
  FanoPlane.relabel fanoLines_plane representative_hasFanoColumns
  HasFanoColumns.relabel exists_fano_columns fano_column_of_degree_three
  fano_eq_of_five_columns column_meets_line_of_five_columns

end CoveringDesigns.StantonGeometry
