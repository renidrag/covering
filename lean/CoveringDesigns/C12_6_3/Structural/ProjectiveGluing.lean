import CoveringDesigns.Foundations.StandardAxioms
import CoveringDesigns.Foundations.BinaryCap
import CoveringDesigns.C11_5_2.Geometry.Fano
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
The projective geometry used to glue the local Stanton planes in the
no-duplicate branch of GPPT 5.9.  The only finite checks concern the fixed
six coordinate hyperplanes in the sixteen-element binary vector space.
No subsets of that space, coverings, or caps are enumerated.
-/

namespace CoveringDesigns.GPPTProjective

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

abbrev V := Fin 4 → ZMod 2

/-- The row whose trace on the six minimum points is empty. -/
def infinity : V := ![0, 1, 1, 1]

/-- The incidence equation for the minimum point `(i,b)`. -/
def lowEquation (i : Fin 3) (b : ZMod 2) (x : V) : ZMod 2 :=
  x i.succ + b * x 0

/-- The quotient by the span of the three pair rows. -/
def pairQuotient (x : V) : ZMod 2 × ZMod 2 :=
  (x 0, x 1 + x 2 + x 3)

/-- The one line missed by all six minimum-point hyperplanes. -/
def exceptionalLine : Finset V :=
  univ.filter (fun x => x ≠ 0 ∧ pairQuotient x = 0)

theorem exceptionalLine_card : exceptionalLine.card = 3 := by
  decide +kernel

/-- Every other line avoiding the empty-trace row lies in a low hyperplane. -/
theorem line_low_or_exceptional : ∀ u v : V,
    u ≠ 0 → v ≠ 0 → u ≠ v →
    u ≠ infinity → v ≠ infinity → u + v ≠ infinity →
    (∃ i : Fin 3, ∃ b : ZMod 2,
      lowEquation i b u = 0 ∧ lowEquation i b v = 0) ∨
    (u ∈ exceptionalLine ∧ v ∈ exceptionalLine) := by
  decide +kernel

theorem lowEquation_add (i : Fin 3) (b : ZMod 2) (u v : V) :
    lowEquation i b (u + v) = lowEquation i b u + lowEquation i b v := by
  simp only [lowEquation, Pi.add_apply, mul_add]
  ring

theorem pairQuotient_add (u v : V) :
    pairQuotient (u + v) = pairQuotient u + pairQuotient v := by
  apply Prod.ext
  · rfl
  · simp only [pairQuotient, Prod.snd_add, Pi.add_apply]
    ring

theorem eq_of_add_eq_zero {u v : V} (h : u + v = 0) : u = v := by
  funext i
  exact CharTwo.add_eq_zero.mp (congrFun h i)

theorem exceptionalLine_add {u v : V} (hu : u ∈ exceptionalLine)
    (hv : v ∈ exceptionalLine) (hne : u ≠ v) : u + v ∈ exceptionalLine := by
  obtain ⟨hu0, huq⟩ := (mem_filter.mp hu).2
  obtain ⟨hv0, hvq⟩ := (mem_filter.mp hv).2
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_, ?_⟩
  · exact fun h => hne (eq_of_add_eq_zero h)
  · rw [pairQuotient_add, huq, hvq, zero_add]

/-- No line of the absence set may lie in one of the six local planes. -/
def LocallySumFree (S : Finset V) : Prop :=
  ∀ i b, ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
    lowEquation i b u = 0 → lowEquation i b v = 0 → u + v ∉ S

/-- Local restrictions leave only the exceptional line as a possible line. -/
theorem sum_in_exceptional {S : Finset V} (hzero : 0 ∉ S)
    (hinfty : infinity ∉ S) (hlocal : LocallySumFree S)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v)
    (hsum : u + v ∈ S) : u ∈ exceptionalLine ∧ v ∈ exceptionalLine := by
  have hu0 : u ≠ 0 := fun h => hzero (h ▸ hu)
  have hv0 : v ≠ 0 := fun h => hzero (h ▸ hv)
  have hui : u ≠ infinity := fun h => hinfty (h ▸ hu)
  have hvi : v ≠ infinity := fun h => hinfty (h ▸ hv)
  have hsi : u + v ≠ infinity := fun h => hinfty (h ▸ hsum)
  rcases line_low_or_exceptional u v hu0 hv0 hne hui hvi hsi with h | h
  · obtain ⟨i, b, hi, hb⟩ := h
    exact False.elim (hlocal i b u hu v hv hne hi hb hsum)
  · exact h

/-- If the exceptional line is present, each nonzero quotient class supplies
at most one further member. -/
theorem card_le_six_of_exceptional_subset {S : Finset V} (hzero : 0 ∉ S)
    (hinfty : infinity ∉ S) (hlocal : LocallySumFree S)
    (hline : exceptionalLine ⊆ S) : S.card ≤ 6 := by
  have hinj : Set.InjOn pairQuotient ↑(S \ exceptionalLine) := by
    intro u hu v hv hq
    obtain ⟨huS, huL⟩ := mem_sdiff.mp hu
    obtain ⟨hvS, hvL⟩ := mem_sdiff.mp hv
    by_contra hne
    have hs : u + v ∈ exceptionalLine := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_, ?_⟩
      · exact fun h => hne (eq_of_add_eq_zero h)
      · rw [pairQuotient_add, hq]
        apply Prod.ext <;> simp [CharTwo.add_self_eq_zero]
    exact huL (sum_in_exceptional hzero hinfty hlocal huS hvS hne (hline hs)).1
  have hsub : (S \ exceptionalLine).image pairQuotient ⊆
      (univ : Finset (ZMod 2 × ZMod 2)).erase 0 := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hq
    obtain ⟨huS, huL⟩ := mem_sdiff.mp hu
    apply mem_erase.mpr
    refine ⟨?_, mem_univ _⟩
    intro hq
    exact huL (mem_filter.mpr ⟨mem_univ _,
      fun h => hzero (h ▸ huS), hq⟩)
  have hrest : (S \ exceptionalLine).card ≤ 3 := by
    rw [← card_image_of_injOn hinj]
    have hc := card_le_card hsub
    have ht : ((univ : Finset (ZMod 2 × ZMod 2)).erase 0).card = 3 := by
      decide +kernel
    rwa [ht] at hc
  have hcard := card_sdiff_add_card_eq_card hline
  rw [exceptionalLine_card] at hcard
  omega

/-- A seven-element absence set obeying the six local Fano restrictions is
a cap in the full projective space. -/
theorem seven_locally_sum_free {S : Finset V} (hcard : S.card = 7)
    (hzero : 0 ∉ S) (hinfty : infinity ∉ S) (hlocal : LocallySumFree S) :
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → u + v ∉ S := by
  intro u hu v hv hne hsum
  obtain ⟨huL, hvL⟩ := sum_in_exceptional hzero hinfty hlocal hu hv hne hsum
  have hsumL := exceptionalLine_add huL hvL hne
  have hline : exceptionalLine ⊆ S := by
    have hthree : ({u, v, u + v} : Finset V).card = 3 := by
      have hu0 : u ≠ 0 := fun h => hzero (h ▸ hu)
      have hv0 : v ≠ 0 := fun h => hzero (h ▸ hv)
      have hus : u ≠ u + v := by simpa using hv0
      have hvs : v ≠ u + v := by simpa using hu0
      simp [hne, hus, hvs]
    have heq : ({u, v, u + v} : Finset V) = exceptionalLine := by
      apply eq_of_subset_of_card_le
      · simpa only [insert_subset_iff, singleton_subset_iff] using ⟨huL, hvL, hsumL⟩
      · rw [hthree, exceptionalLine_card]
    rw [← heq]
    simpa only [insert_subset_iff, singleton_subset_iff] using ⟨hu, hv, hsum⟩
  have hbound := card_le_six_of_exceptional_subset hzero hinfty hlocal hline
  omega

/-- The global cap supplies the normal of the underlying high-point column. -/
theorem seven_locally_sum_free_hyperplane {S : Finset V} (hcard : S.card = 7)
    (hzero : 0 ∉ S) (hinfty : infinity ∉ S) (hlocal : LocallySumFree S) :
    ∃ n : V, n ≠ 0 ∧ ∀ x ∈ S, BinaryCap.dot n x = 1 :=
  BinaryCap.seven_cap_affine_hyperplane S hcard hzero
    (seven_locally_sum_free hcard hzero hinfty hlocal)

abbrev LowPoint := Fin 3 × ZMod 2

/-- The seven nonzero row vectors in a specified minimum-point plane. -/
abbrev LowRows (p : LowPoint) :=
  {x : V // x ≠ 0 ∧ lowEquation p.1 p.2 x = 0}

/-- Binary coordinates with the row order of the fixed Stanton Fano plane. -/
def fanoVector : Fin 7 → (Fin 3 → ZMod 2) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1],
    ![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]

/-- Solve the one low-point equation in terms of three free coordinates. -/
def lowVector (p : LowPoint) (x : Fin 3 → ZMod 2) : V :=
  if p.1 = 0 then ![x 0, p.2 * x 0, x 1, x 2]
  else if p.1 = 1 then ![x 0, x 1, p.2 * x 0, x 2]
  else ![x 0, x 1, x 2, p.2 * x 0]

section CoordinateChecks

set_option synthInstance.maxSize 2048

theorem fanoVector_low (p : LowPoint) (i : Fin 7) :
    lowVector p (fanoVector i) ≠ 0 ∧
      lowEquation p.1 p.2 (lowVector p (fanoVector i)) = 0 := by
  have h : ∀ p : LowPoint, ∀ i : Fin 7,
      lowVector p (fanoVector i) ≠ 0 ∧
        lowEquation p.1 p.2 (lowVector p (fanoVector i)) = 0 := by
    decide +kernel
  exact h p i

theorem fanoVector_low_injective (p : LowPoint) :
    Function.Injective (fun i => lowVector p (fanoVector i)) := by
  have h : ∀ p : LowPoint, ∀ i j : Fin 7,
      lowVector p (fanoVector i) = lowVector p (fanoVector j) → i = j := by
    decide +kernel
  exact h p

theorem fanoVector_low_surjective (p : LowPoint) (x : V)
    (hx : x ≠ 0) (hp : lowEquation p.1 p.2 x = 0) :
    ∃ i, lowVector p (fanoVector i) = x := by
  have h : ∀ p : LowPoint, ∀ x : V,
      x ≠ 0 → lowEquation p.1 p.2 x = 0 →
        ∃ i, lowVector p (fanoVector i) = x := by
    decide +kernel
  exact h p x hx hp

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

/-- Addition on each displayed triple is binary vector addition. -/
theorem fanoVector_line_add : ∀ i j : Fin 7,
    ∀ L ∈ StantonGeometry.fanoLines, i ∈ L → j ∈ L → i ≠ j →
      ∃ k ∈ L, fanoVector k = fanoVector i + fanoVector j := by
  decide +kernel

end CoordinateChecks

noncomputable def localRowEquiv (p : LowPoint) : Fin 7 ≃ LowRows p :=
  Equiv.ofBijective (fun i => ⟨lowVector p (fanoVector i), fanoVector_low p i⟩)
    ⟨fun _ _ h => fanoVector_low_injective p (congrArg Subtype.val h), by
      intro x
      obtain ⟨i, hi⟩ := fanoVector_low_surjective p x.val x.property.1 x.property.2
      exact ⟨i, Subtype.ext hi⟩⟩

/-- The ordinary coordinate Fano plane on a low-point hyperplane. -/
noncomputable def coordinatePlane (p : LowPoint) : Family (LowRows p) :=
  relabel (localRowEquiv p) StantonGeometry.fanoLines

theorem coordinatePlane_fano (p : LowPoint) :
    StantonGeometry.FanoPlane (coordinatePlane p) :=
  StantonGeometry.fanoLines_plane.relabel (localRowEquiv p)

/-- The restriction of another low-point column to these seven rows. -/
def lowColumn (p q : LowPoint) : Finset (LowRows p) :=
  univ.filter fun x => lowEquation q.1 q.2 x.val = 0

section CoordinateColumnChecks

set_option synthInstance.maxSize 2048

theorem lowColumn_mem : ∀ p q : LowPoint,
    q ≠ p → lowColumn p q ∈ coordinatePlane p := by
  decide +kernel

theorem lowColumn_injective : ∀ p q r : LowPoint,
    q ≠ p → r ≠ p → lowColumn p q = lowColumn p r → q = r := by
  decide +kernel

end CoordinateColumnChecks

theorem lowColumn_card (p q : LowPoint) (hqp : q ≠ p) :
    (lowColumn p q).card = 3 :=
  (coordinatePlane_fano p).line_card _ (lowColumn_mem p q hqp)

theorem lowVector_add (p : LowPoint) (u v : Fin 3 → ZMod 2) :
    lowVector p (u + v) = lowVector p u + lowVector p v := by
  rcases p with ⟨i, b⟩
  fin_cases i <;> ext j <;> fin_cases j <;> simp [lowVector, mul_add]

theorem coordinatePlane_add_closed (p : LowPoint) {L : Finset (LowRows p)}
    (hL : L ∈ coordinatePlane p) {u v : LowRows p}
    (hu : u ∈ L) (hv : v ∈ L) (hne : u ≠ v) :
    ∃ w ∈ L, w.val = u.val + v.val := by
  obtain ⟨M, hM, rfl⟩ := mem_map.mp hL
  obtain ⟨i, hi, rfl⟩ := mem_map.mp hu
  obtain ⟨j, hj, rfl⟩ := mem_map.mp hv
  have hij : i ≠ j := fun h => hne (congrArg (localRowEquiv p) h)
  obtain ⟨k, hk, hsum⟩ := fanoVector_line_add i j M hM hi hj hij
  refine ⟨localRowEquiv p k, mem_map.mpr ⟨k, hk, rfl⟩, ?_⟩
  change lowVector p (fanoVector k) =
    lowVector p (fanoVector i) + lowVector p (fanoVector j)
  rw [hsum, lowVector_add]

/-- Blocking all seven local projective lines forbids a line in the absence
set. This is the coordinate consequence used after the Stanton bridge. -/
theorem locallySumFree_of_line_blocking {S : Finset V}
    (hzero : 0 ∉ S)
    (hblock : ∀ p : LowPoint, ∀ L ∈ coordinatePlane p,
      ∃ x ∈ L, x.val ∉ S) : LocallySumFree S := by
  intro i b u hu v hv hne hup hvp hsum
  let p : LowPoint := (i, b)
  let u' : LowRows p := ⟨u, fun h => hzero (h ▸ hu), hup⟩
  let v' : LowRows p := ⟨v, fun h => hzero (h ▸ hv), hvp⟩
  have hne' : u' ≠ v' := fun h => hne (congrArg Subtype.val h)
  obtain ⟨L, hL, huL, hvL⟩ := (coordinatePlane_fano p).pair_exists u' v' hne'
  obtain ⟨w, hwL, hw⟩ := coordinatePlane_add_closed p hL huL hvL hne'
  have huw : u' ≠ w := by
    intro he
    have hz : v = 0 := by
      have hx : u = u + v := (congrArg Subtype.val he).trans hw
      simpa using hx
    exact hzero (hz ▸ hv)
  have hvw : v' ≠ w := by
    intro he
    have hz : u = 0 := by
      have hx : v = u + v := (congrArg Subtype.val he).trans hw
      simpa using hx
    exact hzero (hz ▸ hu)
  have hthree : ({u', v', w} : Finset (LowRows p)) = L := by
    apply eq_of_subset_of_card_le
    · simpa only [insert_subset_iff, singleton_subset_iff] using ⟨huL, hvL, hwL⟩
    · rw [(coordinatePlane_fano p).line_card L hL]
      simp [hne', huw, hvw]
  obtain ⟨x, hx, hxS⟩ := hblock p L hL
  rw [← hthree] at hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hxS hu
  · exact hxS hv
  · exact hxS (hw ▸ hsum)

section ArbitraryCover

variable {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}

/-- The normalized six-point projection, to be supplied by the structural
trace argument. It identifies actual blocks and actual minimum points. -/
structure ProjectionLabelling (C : Family α) where
  pointEquiv : ↥(minimumPoints C 7) ≃ LowPoint
  rowEquiv : ↥C ≃ {x : V // x ≠ 0}
  incidence : ∀ p B, p.val ∈ B.val ↔
    lowEquation (pointEquiv p).1 (pointEquiv p).2 (rowEquiv B).val = 0

namespace ProjectionLabelling

theorem minimum_card (R : ProjectionLabelling C) : (minimumPoints C 7).card = 6 := by
  have h := Fintype.card_congr R.pointEquiv
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, ZMod.card] using h

/-- Deleting the distinguished point is a bijection on its incident blocks. -/
noncomputable def linkRowEquiv (C : Family α) (p : α) :
    ↥(star C p) ≃ ↥(link C p) :=
  Equiv.ofBijective
    (fun B => ⟨B.val.subtype (· ≠ p), mem_image.mpr ⟨B.val, B.property, rfl⟩⟩)
    ⟨by
      intro B D he
      apply Subtype.ext
      ext q
      by_cases hq : q = p
      · subst q
        exact iff_of_true (mem_filter.mp B.property).2 (mem_filter.mp D.property).2
      · have h := congrArg (fun A : ↥(link C p) => (⟨q, hq⟩ : {q : α // q ≠ p}) ∈ A.val) he
        simpa using h,
      by
        intro D
        obtain ⟨B, hB, he⟩ := mem_image.mp D.property
        exact ⟨⟨B, hB⟩, Subtype.ext he⟩⟩

/-- Restrict the global row labels to one minimum-point hyperplane. -/
def starCoordinates (R : ProjectionLabelling C) (p : ↥(minimumPoints C 7)) :
    ↥(star C p.val) ≃ LowRows (R.pointEquiv p) where
  toFun B := ⟨(R.rowEquiv ⟨B.val, (mem_filter.mp B.property).1⟩).val,
    (R.rowEquiv ⟨B.val, (mem_filter.mp B.property).1⟩).property,
    (R.incidence p _).mp (mem_filter.mp B.property).2⟩
  invFun x := ⟨(R.rowEquiv.symm ⟨x.val, x.property.1⟩).val,
    mem_filter.mpr ⟨(R.rowEquiv.symm ⟨x.val, x.property.1⟩).property,
      (R.incidence p _).mpr (by simpa using x.property.2)⟩⟩
  left_inv B := by
    apply Subtype.ext
    change (R.rowEquiv.symm (R.rowEquiv ⟨B.val, (mem_filter.mp B.property).1⟩)).val = B.val
    simp
  right_inv x := by
    apply Subtype.ext
    change (R.rowEquiv (R.rowEquiv.symm ⟨x.val, x.property.1⟩)).val = x.val
    simp

/-- Actual rows of a Stanton link, labelled by their ambient binary vectors. -/
noncomputable def linkCoordinates (R : ProjectionLabelling C)
    (p : ↥(minimumPoints C 7)) : ↥(link C p.val) ≃ LowRows (R.pointEquiv p) :=
  (linkRowEquiv C p.val).symm.trans (R.starCoordinates p)

theorem linkCoordinates_mem (R : ProjectionLabelling C)
    (p : ↥(minimumPoints C 7)) (x : LowRows (R.pointEquiv p))
    (q : {q : α // q ≠ p.val}) :
    q ∈ ((R.linkCoordinates p).symm x).val ↔
      q.val ∈ (R.rowEquiv.symm ⟨x.val, x.property.1⟩).val := by
  change q ∈ ((R.rowEquiv.symm ⟨x.val, x.property.1⟩).val.subtype (· ≠ p.val)) ↔ _
  exact mem_subtype

/-- The five other minimum columns become the five fixed coordinate lines. -/
theorem linkCoordinates_column (R : ProjectionLabelling C)
    (p q : ↥(minimumPoints C 7)) (hqp : q.val ≠ p.val) :
    (StantonGeometry.incidentRows (link C p.val) ⟨q.val, hqp⟩).map
      (R.linkCoordinates p).toEmbedding =
      lowColumn (R.pointEquiv p) (R.pointEquiv q) := by
  ext x
  simp only [mem_map_equiv, StantonGeometry.incidentRows, mem_filter,
    mem_univ, true_and, lowColumn]
  rw [R.linkCoordinates_mem]
  exact (R.incidence q _).trans (by simp)

end ProjectionLabelling

end ArbitraryCover

#guard_standard_axioms exceptionalLine_card line_low_or_exceptional
  lowEquation_add pairQuotient_add exceptionalLine_add sum_in_exceptional
  card_le_six_of_exceptional_subset seven_locally_sum_free
  seven_locally_sum_free_hyperplane coordinatePlane_fano lowColumn_mem
  lowColumn_injective lowColumn_card coordinatePlane_add_closed
  locallySumFree_of_line_blocking
  ProjectionLabelling.minimum_card ProjectionLabelling.linkCoordinates_column

end CoveringDesigns.GPPTProjective
