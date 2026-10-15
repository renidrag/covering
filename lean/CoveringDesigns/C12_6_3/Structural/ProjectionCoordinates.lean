import CoveringDesigns.C12_6_3.Structural.ProjectionFrame
import CoveringDesigns.C12_6_3.Structural.ProjectiveGluing

/-!
Coordinates for the six-point projection.  The only finite calculation is
the incidence table of the fifteen nonzero binary four-vectors on six fixed
coordinate hyperplanes.  The equivalences for an arbitrary covering are
deduced from its `LowProjectionFrame`.
-/

namespace CoveringDesigns.GPPTStructural

open Finset GPPTProjective

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- One of the three pairs in the fixed six-point coordinate set. -/
def coordinatePair (i : Fin 3) : Finset LowPoint :=
  univ.filter fun p => p.1 = i

/-- The trace of a projective row on the six low-point columns. -/
def coordinateTrace (v : V) : Finset LowPoint :=
  univ.filter fun p => lowEquation p.1 p.2 v = 0

/-- The fifteen traces on three labelled pairs. -/
def coordinateTraces : Family LowPoint :=
  insert ∅ ((univ.image coordinatePair) ∪
    (univ.image fun i => univ \ coordinatePair i) ∪
    pairTransversals univ coordinatePair)

section FixedCoordinateChecks

set_option synthInstance.maxSize 2048

theorem coordinateTrace_range :
    (univ.filter fun v : V => v ≠ 0).image coordinateTrace = coordinateTraces := by
  decide +kernel

theorem coordinateTrace_injective : Function.Injective coordinateTrace := by
  have h : ∀ u v : V, coordinateTrace u = coordinateTrace v → u = v := by
    decide +kernel
  exact h

theorem coordinateTrace_infinity : coordinateTrace infinity = ∅ := by
  decide +kernel

theorem infinity_ne_zero : infinity ≠ 0 := by
  decide +kernel

end FixedCoordinateChecks

namespace ThreePairPartition

variable {α : Type*} [DecidableEq α] {P : Finset α} (F : ThreePairPartition P)

/-- Arbitrarily orient each of the three two-point pairs. -/
noncomputable def pairEquiv (i : Fin 3) : {p // p ∈ F.pairs i} ≃ ZMod 2 :=
  Fintype.equivOfCardEq (by simp [F.pairs_card])

noncomputable def point (p : LowPoint) : α :=
  ((F.pairEquiv p.1).symm p.2).val

theorem point_mem_pair (p : LowPoint) : F.point p ∈ F.pairs p.1 :=
  ((F.pairEquiv p.1).symm p.2).property

theorem point_mem (p : LowPoint) : F.point p ∈ P :=
  F.pairs_subset p.1 (F.point_mem_pair p)

theorem point_injective : Function.Injective F.point := by
  rintro ⟨i, b⟩ ⟨j, c⟩ he
  have hij : i = j := by
    by_contra hn
    exact disjoint_left.mp (F.pairs_disjoint hn)
      (F.point_mem_pair (i, b)) (he ▸ F.point_mem_pair (j, c))
  subst j
  congr 1
  apply (F.pairEquiv i).symm.injective
  exact Subtype.ext he

theorem point_surjective (p : α) (hp : p ∈ P) : ∃ q, F.point q = p := by
  rw [← F.pairs_union] at hp
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
  refine ⟨(i, F.pairEquiv i ⟨p, hi⟩), ?_⟩
  simp [point]

/-- Coordinates on the six points, determined by an orientation of each pair. -/
noncomputable def pointEquiv : {p // p ∈ P} ≃ LowPoint :=
  (Equiv.ofBijective (fun p => (⟨F.point p, F.point_mem p⟩ : {p // p ∈ P}))
    ⟨fun _ _ h => F.point_injective (congrArg Subtype.val h), by
      intro p
      obtain ⟨q, hq⟩ := F.point_surjective p.val p.property
      exact ⟨q, Subtype.ext hq⟩⟩).symm

@[simp] theorem pointEquiv_symm_val (p : LowPoint) :
    (F.pointEquiv.symm p).val = F.point p := rfl

theorem point_mem_pair_iff (p : LowPoint) (i : Fin 3) :
    F.point p ∈ F.pairs i ↔ p.1 = i := by
  constructor
  · intro hp
    by_contra hn
    exact disjoint_left.mp (F.pairs_disjoint hn) (F.point_mem_pair p) hp
  · rintro rfl
    exact F.point_mem_pair p

/-- Pull a subset of the original points back to the six labelled points. -/
noncomputable def normalize (T : Finset α) : Finset LowPoint :=
  univ.filter fun p => F.point p ∈ T

@[simp] theorem mem_normalize (p : LowPoint) (T : Finset α) :
    p ∈ F.normalize T ↔ F.point p ∈ T := by
  simp [normalize]

theorem image_normalize {T : Finset α} (hT : T ⊆ P) :
    (F.normalize T).image F.point = T := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact (F.mem_normalize q T).mp hq
  · intro hp
    obtain ⟨q, rfl⟩ := F.point_surjective p (hT hp)
    exact mem_image.mpr ⟨q, (F.mem_normalize q T).mpr hp, rfl⟩

theorem normalize_injective {T U : Finset α} (hT : T ⊆ P) (hU : U ⊆ P)
    (he : F.normalize T = F.normalize U) : T = U := by
  rw [← F.image_normalize hT, ← F.image_normalize hU, he]

theorem normalize_card {T : Finset α} (hT : T ⊆ P) :
    (F.normalize T).card = T.card := by
  calc
    (F.normalize T).card = ((F.normalize T).image F.point).card :=
      (card_image_of_injective _ F.point_injective).symm
    _ = T.card := congrArg Finset.card (F.image_normalize hT)

@[simp] theorem normalize_empty : F.normalize ∅ = ∅ := by
  ext p
  simp

@[simp] theorem normalize_inter (T U : Finset α) :
    F.normalize (T ∩ U) = F.normalize T ∩ F.normalize U := by
  ext p
  simp

@[simp] theorem normalize_universe : F.normalize P = univ := by
  ext p
  simp [F.point_mem]

@[simp] theorem normalize_pair (i : Fin 3) :
    F.normalize (F.pairs i) = coordinatePair i := by
  ext p
  simp [coordinatePair, F.point_mem_pair_iff]

@[simp] theorem normalize_complement_pair (i : Fin 3) :
    F.normalize (P \ F.pairs i) = univ \ coordinatePair i := by
  ext p
  simp [coordinatePair, F.point_mem, F.point_mem_pair_iff]

theorem normalize_mem_transversals {T : Finset α} (hT : T ⊆ P) :
    F.normalize T ∈ pairTransversals univ coordinatePair ↔
      T ∈ pairTransversals P F.pairs := by
  simp only [pairTransversals, mem_filter, mem_powersetCard, subset_univ,
    true_and, hT, F.normalize_card hT]
  have hi (i : Fin 3) : (F.normalize T ∩ coordinatePair i).card =
      (T ∩ F.pairs i).card := by
    rw [← F.normalize_pair, ← F.normalize_inter]
    exact F.normalize_card (inter_subset_right.trans (F.pairs_subset i))
  simp only [hi]

theorem image_point_subset (U : Finset LowPoint) : U.image F.point ⊆ P := by
  intro p hp
  obtain ⟨q, _, rfl⟩ := mem_image.mp hp
  exact F.point_mem q

@[simp] theorem normalize_image_point (U : Finset LowPoint) :
    F.normalize (U.image F.point) = U := by
  ext p
  simp [F.point_injective.eq_iff]

theorem normalize_transversals :
    (pairTransversals P F.pairs).image F.normalize =
      pairTransversals univ coordinatePair := by
  ext U
  constructor
  · intro hU
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hU
    have hTP := (mem_powersetCard.mp (mem_filter.mp hT).1).1
    exact (F.normalize_mem_transversals hTP).mpr hT
  · intro hU
    refine mem_image.mpr ⟨U.image F.point, ?_, F.normalize_image_point U⟩
    apply (F.normalize_mem_transversals (F.image_point_subset U)).mp
    simpa using hU

end ThreePairPartition

namespace LowProjectionFrame

variable {α : Type*} [DecidableEq α] [Fintype α] {C : Family α}
    (F : LowProjectionFrame C)

/-- Label the six minimum points by a pair index and a binary orientation. -/
noncomputable def pointEquiv : {p // p ∈ minimumPoints C 7} ≃ LowPoint :=
  F.toThreePairPartition.pointEquiv

theorem normalized_traces :
    C.image (fun B => F.toThreePairPartition.normalize (minimumPoints C 7 ∩ B)) =
      coordinateTraces := by
  change C.image (F.toThreePairPartition.normalize ∘
    (fun B => minimumPoints C 7 ∩ B)) = coordinateTraces
  rw [← image_image, F.traces_eq]
  simp only [image_insert, image_union, image_image, Function.comp_def,
    ThreePairPartition.normalize_empty, ThreePairPartition.normalize_pair,
    ThreePairPartition.normalize_complement_pair,
    ThreePairPartition.normalize_transversals]
  rfl

theorem exists_row_coordinates (B : {B // B ∈ C}) :
    ∃ v : V, v ≠ 0 ∧ coordinateTrace v =
      F.toThreePairPartition.normalize (minimumPoints C 7 ∩ B.val) := by
  have hm : F.toThreePairPartition.normalize (minimumPoints C 7 ∩ B.val) ∈
      coordinateTraces := by
    rw [← F.normalized_traces]
    exact mem_image.mpr ⟨B.val, B.property, rfl⟩
  rw [← coordinateTrace_range] at hm
  obtain ⟨v, hv, he⟩ := mem_image.mp hm
  exact ⟨v, (mem_filter.mp hv).2, he⟩

noncomputable def rowVector (B : {B // B ∈ C}) : {v : V // v ≠ 0} :=
  ⟨(F.exists_row_coordinates B).choose,
    (F.exists_row_coordinates B).choose_spec.1⟩

theorem rowVector_trace (B : {B // B ∈ C}) :
    coordinateTrace (F.rowVector B).val =
      F.toThreePairPartition.normalize (minimumPoints C 7 ∩ B.val) :=
  (F.exists_row_coordinates B).choose_spec.2

theorem rowVector_injective : Function.Injective F.rowVector := by
  intro B D he
  apply Subtype.ext
  apply F.trace_injective B.property D.property
  apply F.toThreePairPartition.normalize_injective inter_subset_left inter_subset_left
  rw [← F.rowVector_trace B, ← F.rowVector_trace D, he]

theorem rowVector_surjective : Function.Surjective F.rowVector := by
  intro v
  have hm : coordinateTrace v.val ∈ coordinateTraces := by
    rw [← coordinateTrace_range]
    exact mem_image.mpr ⟨v.val, mem_filter.mpr ⟨mem_univ _, v.property⟩, rfl⟩
  rw [← F.normalized_traces] at hm
  obtain ⟨B, hB, he⟩ := mem_image.mp hm
  refine ⟨⟨B, hB⟩, Subtype.ext ?_⟩
  apply coordinateTrace_injective
  exact (F.rowVector_trace ⟨B, hB⟩).trans he

/-- The fifteen covering blocks are precisely the nonzero projective rows. -/
noncomputable def rowEquiv : {B // B ∈ C} ≃ {v : V // v ≠ 0} :=
  Equiv.ofBijective F.rowVector ⟨F.rowVector_injective, F.rowVector_surjective⟩

theorem rowEquiv_trace (B : {B // B ∈ C}) :
    coordinateTrace (F.rowEquiv B).val =
      F.toThreePairPartition.normalize (minimumPoints C 7 ∩ B.val) :=
  F.rowVector_trace B

/-- Incidence at a minimum point is its specified binary linear equation. -/
theorem mem_iff_lowEquation (p : {p // p ∈ minimumPoints C 7})
    (B : {B // B ∈ C}) :
    p.val ∈ B.val ↔
      lowEquation (F.pointEquiv p).1 (F.pointEquiv p).2 (F.rowEquiv B).val = 0 := by
  have hp : F.toThreePairPartition.point (F.pointEquiv p) = p.val :=
    congrArg Subtype.val (F.pointEquiv.symm_apply_apply p)
  have he := congrArg (fun T => F.pointEquiv p ∈ T) (F.rowEquiv_trace B)
  simpa only [coordinateTrace, mem_filter, mem_univ, true_and,
    ThreePairPartition.mem_normalize, mem_inter, hp, p.property] using Iff.of_eq he.symm

/-- The distinguished projective row is exactly the row with empty low trace. -/
theorem rowEquiv_eq_infinity_iff (B : {B // B ∈ C}) :
    (F.rowEquiv B).val = infinity ↔ minimumPoints C 7 ∩ B.val = ∅ := by
  constructor
  · intro h
    apply F.toThreePairPartition.normalize_injective inter_subset_left (empty_subset _)
    rw [← F.rowEquiv_trace B, h, coordinateTrace_infinity,
      ThreePairPartition.normalize_empty]
  · intro h
    apply coordinateTrace_injective
    rw [F.rowEquiv_trace B, h, ThreePairPartition.normalize_empty,
      coordinateTrace_infinity]

/-- Package the structural projection as the labelling used by the local
Fano-plane and global projective gluing arguments. -/
noncomputable def toProjectionLabelling : GPPTProjective.ProjectionLabelling C where
  pointEquiv := F.pointEquiv
  rowEquiv := F.rowEquiv
  incidence := F.mem_iff_lowEquation

end LowProjectionFrame

#guard_standard_axioms coordinateTrace_range coordinateTrace_injective
  coordinateTrace_infinity infinity_ne_zero ThreePairPartition.pointEquiv
  LowProjectionFrame.pointEquiv LowProjectionFrame.rowEquiv
  LowProjectionFrame.mem_iff_lowEquation LowProjectionFrame.rowEquiv_eq_infinity_iff
  LowProjectionFrame.toProjectionLabelling

end CoveringDesigns.GPPTStructural
