import CoveringDesigns.C12_6_3.Structural.ProjectionCoordinates
import CoveringDesigns.C12_6_3.Structural.ProjectiveTemplate
import CoveringDesigns.C12_6_3.Structural.Branching

/-! The arbitrary-cover bridge for the projective branch. The row labelling
comes from the six-point projection. Five degree-three columns identify each
local Fano plane; its line-blocking property supplies every underlying column
hyperplane. Thus the resulting projective core is a Figure 1 completion. -/

namespace CoveringDesigns.GPPTProjective

open Finset StantonGeometry GPPTStructural

variable {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}

namespace ProjectionLabelling

/-- The five other minimum points determine the coordinate Fano plane in
each link. Every original point therefore meets every coordinate line. -/
theorem column_blocks_lines (R : ProjectionLabelling C)
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    (q : α) (p : LowPoint) {L : Finset (LowRows p)}
    (hL : L ∈ coordinatePlane p) :
    ∃ x ∈ L, q ∈ (R.rowEquiv.symm ⟨x.val, x.property.1⟩).val := by
  classical
  obtain ⟨p, rfl⟩ := R.pointEquiv.surjective p
  let e := R.linkCoordinates p
  let I := (minimumPoints C 7).subtype (· ≠ p.val)
  have hI : I.card = 5 := by
    dsimp only [I]
    rw [card_subtype]
    have he : (minimumPoints C 7).filter (· ≠ p.val) =
        (minimumPoints C 7).erase p.val := by
      ext x
      simp [and_comm]
    rw [he, card_erase_of_mem p.property, R.minimum_card]
  have hcol (r : {r : α // r ≠ p.val}) (hr : r ∈ I) :
      (incidentRows (link C p.val) r).map e.toEmbedding =
        lowColumn (R.pointEquiv p) (R.pointEquiv ⟨r.val, mem_subtype.mp hr⟩) :=
    R.linkCoordinates_column p ⟨r.val, mem_subtype.mp hr⟩ r.property
  have hne (r : {r : α // r ≠ p.val}) (hr : r ∈ I) :
      R.pointEquiv ⟨r.val, mem_subtype.mp hr⟩ ≠ R.pointEquiv p := by
    intro he
    exact r.property (congrArg Subtype.val (R.pointEquiv.injective he))
  let G := relabel e.symm (coordinatePlane (R.pointEquiv p))
  have hG : FanoPlane G := (coordinatePlane_fano _).relabel e.symm
  have hknown (r : {r : α // r ≠ p.val}) (hr : r ∈ I) :
      incidentRows (link C p.val) r ∈ G := by
    have hh := lowColumn_mem _ _ (hne r hr)
    rw [← hcol r hr] at hh
    have hm := (mem_relabel e.symm _ _).mpr hh
    simpa [map_map] using hm
  have hd (r : {r : α // r ≠ p.val}) (hr : r ∈ I) :
      degree (link C p.val) r = 3 := by
    have hh := congrArg Finset.card (hcol r hr)
    simpa only [card_map, incidentRows_card, lowColumn_card _ _ (hne r hr)] using hh
  have hi : Set.InjOn (incidentRows (link C p.val)) I := by
    intro r hr s hs he
    have hh := congrArg (fun T => T.map e.toEmbedding) he
    rw [hcol r hr, hcol s hs] at hh
    have he' := lowColumn_injective _ _ _ (hne r hr) (hne s hs) hh
    have heval : r.val = s.val := congrArg
      (fun x : ↥(minimumPoints C 7) => x.val) (R.pointEquiv.injective he')
    exact Subtype.ext heval
  by_cases hqp : q = p.val
  · have hLn : L.Nonempty := card_pos.mp (by
      rw [(coordinatePlane_fano _).line_card L hL]; decide)
    obtain ⟨x, hx⟩ := hLn
    refine ⟨x, hx, ?_⟩
    rw [hqp]
    exact (R.incidence p _).mpr (by simpa using x.property.2)
  · have hL' : L.map e.symm.toEmbedding ∈ G := (mem_relabel e.symm _ _).mpr hL
    have hp : degree C p.val = 7 := (mem_filter.mp p.property).2
    obtain ⟨B, hB⟩ := column_meets_line_of_five_columns
      (by rw [complement_point_card, hn]) (link_isCover hC p.val)
      (by rwa [link_card]) hG I (by omega) hd hi hknown
      (⟨q, hqp⟩ : {q : α // q ≠ p.val}) hL'
    have hm := (mem_inter.mp hB).1
    have hqB := (mem_filter.mp (mem_inter.mp hB).2).2
    refine ⟨e B, by simpa using hm, ?_⟩
    apply (R.linkCoordinates_mem p (e B) ⟨q, hqp⟩).mp
    simpa only [e, Equiv.symm_apply_apply] using hqB

/-- The absent rows of a point, expressed in the global binary labels. -/
def absentRows (R : ProjectionLabelling C) (q : α) : Finset V :=
  (univ.filter (fun B : ↥C => q ∉ B.val)).image (fun B => (R.rowEquiv B).val)

theorem mem_absentRows (R : ProjectionLabelling C) (q : α) (v : {x : V // x ≠ 0}) :
    v.val ∈ R.absentRows q ↔ q ∉ (R.rowEquiv.symm v).val := by
  constructor
  · intro hv
    obtain ⟨B, hB, he⟩ := mem_image.mp hv
    have he' : R.rowEquiv B = v := Subtype.ext he
    have hb : B = R.rowEquiv.symm v := (R.rowEquiv.eq_symm_apply).mpr he'
    simpa only [hb] using (mem_filter.mp hB).2
  · intro hq
    exact mem_image.mpr ⟨R.rowEquiv.symm v, mem_filter.mpr ⟨mem_univ _, hq⟩, by simp⟩

theorem zero_not_absentRows (R : ProjectionLabelling C) (q : α) : 0 ∉ R.absentRows q := by
  intro h
  obtain ⟨B, _, he⟩ := mem_image.mp h
  exact (R.rowEquiv B).property he

theorem absentRows_card (R : ProjectionLabelling C) (q : α)
    (hb : C.card = 15) (hq : degree C q = 8) : (R.absentRows q).card = 7 := by
  have hi : Function.Injective (fun B : ↥C => (R.rowEquiv B).val) :=
    fun _ _ h => R.rowEquiv.injective (Subtype.ext h)
  rw [absentRows, card_image_of_injective _ hi]
  have hs := card_filter_add_card_filter_not (s := (univ : Finset ↥C))
    (p := fun B => q ∈ B.val)
  change (incidentRows C q).card + _ = _ at hs
  rw [incidentRows_card, card_univ, Fintype.card_coe, hb, hq] at hs
  omega

/-- The empty minimum-point trace is the block of all six other points. -/
theorem infinity_not_absentRows (R : ProjectionLabelling C)
    (hn : Fintype.card α = 12) (hu : Uniform C 6) {q : α} (hq : degree C q ≠ 7) :
    infinity ∉ R.absentRows q := by
  let v : {x : V // x ≠ 0} := ⟨infinity, infinity_ne_zero⟩
  let B := R.rowEquiv.symm v
  have hlow : ∀ p : LowPoint, lowEquation p.1 p.2 infinity ≠ 0 := by decide +kernel
  have hs : B.val ⊆ univ \ minimumPoints C 7 := by
    intro x hx
    apply mem_sdiff.mpr
    refine ⟨mem_univ _, ?_⟩
    intro hxp
    have he := (R.incidence ⟨x, hxp⟩ B).mp hx
    have he' : lowEquation (R.pointEquiv ⟨x, hxp⟩).1
        (R.pointEquiv ⟨x, hxp⟩).2 infinity = 0 := by simpa [B, v] using he
    exact hlow _ he'
  have he : B.val = univ \ minimumPoints C 7 := by
    apply eq_of_subset_of_card_le hs
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn, R.minimum_card, hu _ B.property]
  have hqB : q ∈ B.val := by
    rw [he]
    exact mem_sdiff.mpr ⟨mem_univ _, fun h => hq (mem_filter.mp h).2⟩
  intro hqv
  exact ((R.mem_absentRows q v).mp hqv) hqB

/-- Stanton's line-blocking property is inherited by each global absence set. -/
theorem absentRows_locallySumFree (R : ProjectionLabelling C)
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (q : α) :
    LocallySumFree (R.absentRows q) := by
  apply locallySumFree_of_line_blocking (R.zero_not_absentRows q)
  intro p L hL
  obtain ⟨x, hx, hq⟩ := R.column_blocks_lines hn hC q p hL
  exact ⟨x, hx, fun hs => ((R.mem_absentRows q ⟨x.val, x.property.1⟩).mp hs) hq⟩

/-- A degree-eight column contains a nonzero projective hyperplane. -/
theorem high_column_normal (R : ProjectionLabelling C)
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card = 15)
    (q : α) (hq : degree C q = 8) :
    ∃ n : V, n ≠ 0 ∧ ∀ B : ↥C,
      BinaryCap.dot n (R.rowEquiv B).val = 0 → q ∈ B.val := by
  obtain ⟨n, hn0, hS⟩ := seven_locally_sum_free_hyperplane
    (R.absentRows_card q hb hq) (R.zero_not_absentRows q)
    (R.infinity_not_absentRows hn hC.1 (by omega)) (R.absentRows_locallySumFree hn hC q)
  refine ⟨n, hn0, ?_⟩
  intro B hB
  by_contra hqB
  have hs : (R.rowEquiv B).val ∈ R.absentRows q :=
    (R.mem_absentRows q (R.rowEquiv B)).mpr (by simpa using hqB)
  have he := hS _ hs
  rw [hB] at he
  exact zero_ne_one he

def lowNormal (p : LowPoint) : V :=
  fun i => if i = 0 then p.2 else if i = p.1.succ then 1 else 0

theorem lowNormal_properties : ∀ p : LowPoint,
    lowNormal p ≠ 0 ∧ ∀ v : V, BinaryCap.dot (lowNormal p) v = lowEquation p.1 p.2 v := by
  decide +kernel

/-- Every column has a projective core: low columns already are hyperplanes,
and the seven-cap argument supplies the high columns. -/
theorem all_column_normals (R : ProjectionLabelling C)
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card = 15)
    (hno : NoDuplicateMinimumTriple C) (q : α) :
    ∃ n : V, n ≠ 0 ∧ ∀ B : ↥C,
      BinaryCap.dot n (R.rowEquiv B).val = 0 → q ∈ B.val := by
  rcases no_duplicate_degree_seven_or_eight hn hC hb hno q with hq | hq
  · let p : ↥(minimumPoints C 7) := ⟨q, mem_filter.mpr ⟨mem_univ _, hq⟩⟩
    refine ⟨lowNormal (R.pointEquiv p), (lowNormal_properties _).1, ?_⟩
    intro B hB
    apply (R.incidence p B).mpr
    rwa [(lowNormal_properties _).2] at hB
  · exact R.high_column_normal hn hC hb q hq

#guard_standard_axioms column_blocks_lines mem_absentRows zero_not_absentRows absentRows_card
  infinity_not_absentRows absentRows_locallySumFree high_column_normal all_column_normals

end ProjectionLabelling

/-- The no-duplicate branch of GPPT's structural reduction. -/
theorem no_duplicate_isomorphicTemplateCompletion {C : Family (Fin 12)}
    (hC : IsCover C 6 3) (hb : C.card = 15) (hno : NoDuplicateMinimumTriple C) :
    IsomorphicTemplateCompletion C := by
  classical
  obtain ⟨F⟩ := exists_low_projection_frame (by simp) hC hb hno
    (fun p q hp hq hpq => minimum_pair_degree_three (by simp) hC hb.le hp hq hpq)
  let R := F.toProjectionLabelling
  choose n hn hcore using R.all_column_normals (by simp) hC hb hno
  apply GPPTProjectiveTemplate.isomorphic_completion_of_normal_cores C hC.1 hb.le n hn
  intro v hv
  let B := R.rowEquiv.symm ⟨v, hv⟩
  refine ⟨B.val, B.property, ?_⟩
  intro q hq
  apply hcore q B
  have he := (mem_filter.mp hq).2
  simpa only [B, Equiv.apply_symm_apply] using he

#guard_standard_axioms no_duplicate_isomorphicTemplateCompletion

end CoveringDesigns.GPPTProjective
