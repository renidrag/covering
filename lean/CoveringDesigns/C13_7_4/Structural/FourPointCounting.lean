import CoveringDesigns.C13_7_4.Structural.SelectedFrame
import CoveringDesigns.C12_6_3.Structural.Frames

/-! The constant-coordinate branch of the four-point obstruction has degree
thirteen: one common row and two rows from each of six edge families. -/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural StantonGeometry

variable {α : Type*} [DecidableEq α]

/-- A point's degrees add across disjoint families of blocks. -/
theorem degree_union_of_disjoint {C D : Family α} (hd : Disjoint C D) (x : α) :
    degree (C ∪ D) x = degree C x + degree D x := by
  unfold degree star
  rw [filter_union, card_union_of_disjoint
    (hd.mono (filter_subset _ _) (filter_subset _ _))]

/-- Degree counts an indexed family without repetitions. -/
theorem degree_image_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Finset α) (hi : Function.Injective B) (x : α) :
    degree (univ.image B) x = (univ.filter fun i => x ∈ B i).card := by
  simp only [degree, star, filter_image]
  exact card_image_of_injective _ hi

theorem degree_biUnion_of_pairwise {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Family α) (hd : Pairwise fun i j => Disjoint (P i) (P j)) (x : α) :
    degree (univ.biUnion P) x = ∑ i, degree (P i) x := by
  unfold degree star
  rw [filter_biUnion]
  apply card_biUnion
  intro i _ j _ hij
  exact (hd hij).mono (filter_subset _ _) (filter_subset _ _)

/-- Adjoining the same root set to root-disjoint traces preserves every
outside point's degree. -/
theorem degree_union_image_of_disjoint (K : Finset α) (R : Family α)
    (hdis : ∀ B ∈ R, Disjoint K B) {x : α} (hx : x ∉ K) :
    degree (R.image fun B => K ∪ B) x = degree R x := by
  unfold degree star
  rw [filter_image]
  have hf : R.filter (fun B => x ∈ K ∪ B) = R.filter (fun B => x ∈ B) := by
    ext B
    simp [hx]
  rw [hf]
  apply card_image_of_injOn
  intro B hB D hD he
  have hB := (mem_filter.mp hB).1
  have hD := (mem_filter.mp hD).1
  ext y
  by_cases hy : y ∈ K
  · have hb : y ∉ B := fun h => disjoint_left.mp (hdis B hB) hy h
    have hd : y ∉ D := fun h => disjoint_left.mp (hdis D hD) hy h
    simp [hb, hd]
  · have hm := congrArg (fun S => y ∈ S) he
    simpa only [mem_union, hy, false_or] using (Eq.to_iff hm)

section Triads

variable [Fintype α] {K : Finset α} (F : RootTriads K)
variable (s : Fin 3 → α) (hs : ∀ j, s j ∈ F.triad j)
include hs

/-- Membership in a marked trace is determined by its own triad and selection. -/
theorem triad_markedRow_mem_iff {x : α} {j : Fin 3} (hx : x ∈ F.triad j) (i : Fin 3) :
    x ∈ markedRow F.triad s i ↔
      (i = j ∧ x = s j) ∨ (i ≠ j ∧ x ≠ s j) := by
  by_cases hij : i = j
  · subst i
    have h := congrArg (fun S => x ∈ S)
      (markedRow_inter_self_triad F.triad s F.pairwise_disjoint hs j)
    simpa [hx] using (Eq.to_iff h)
  · have h := congrArg (fun S => x ∈ S)
      (markedRow_inter_other_triad F.triad s F.pairwise_disjoint hs hij)
    simpa [hx, hij] using (Eq.to_iff h)

theorem triad_markedRow_injective : Function.Injective (markedRow F.triad s) := by
  intro i j he
  by_contra hij
  have hm : s i ∈ markedRow F.triad s i := mem_union_left _ (mem_singleton_self _)
  rw [he] at hm
  have h := (triad_markedRow_mem_iff F s hs (hs i) j).mp hm
  simp only [and_true, ne_eq, not_true_eq_false, and_false, or_false] at h
  exact hij h.symm

/-- The selected point has marked-row degree one; the other two points in
its triad have marked-row degree two. -/
theorem triad_marked_degree {x : α} {j : Fin 3} (hx : x ∈ F.triad j) :
    degree (univ.image (markedRow F.triad s)) x = if x = s j then 1 else 2 := by
  rw [degree_image_of_injective _ (triad_markedRow_injective F s hs)]
  by_cases hxs : x = s j
  · rw [ite_eq_left hxs]
    have hf : (univ.filter fun i => x ∈ markedRow F.triad s i) = {j} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      rw [triad_markedRow_mem_iff F s hs hx]
      simp only [hxs, and_true, ne_eq, not_true_eq_false, and_false, or_false]
    rw [hf, card_singleton]
  · rw [ite_eq_right hxs]
    have hf : (univ.filter fun i => x ∈ markedRow F.triad s i) = univ.erase j := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      rw [triad_markedRow_mem_iff F s hs hx]
      simp [hxs]
    rw [hf, card_erase_of_mem (mem_univ j)]
    rfl

/-- A short trace containing all three selected points is different from
all marked traces. -/
theorem short_ne_markedRow (U : Finset α) (hU : ∀ j, s j ∈ U) (i : Fin 3) :
    U ≠ markedRow F.triad s i := by
  obtain ⟨j, hji⟩ := exists_ne i
  intro he
  have hm := hU j
  rw [he] at hm
  have h := (triad_markedRow_mem_iff F s hs (hs j) i).mp hm
  simp [hji.symm] at h

/-- Outside the short trace's two additions, every outside-root point occurs
exactly twice among the three marked traces and the short trace. -/
theorem trace_family_degree_two (U A : Finset α)
    (hU : univ.image s ⊆ U) (hA : U \ univ.image s = A)
    {x : α} (hxK : x ∉ K) (hxA : x ∉ A) :
    degree (insert U (univ.image (markedRow F.triad s))) x = 2 := by
  have hu : x ∈ K ∪ univ.biUnion F.triad := by rw [F.spans]; exact mem_univ _
  obtain ⟨j, _, hxj⟩ := mem_biUnion.mp ((mem_union.mp hu).resolve_left hxK)
  have hUnot : U ∉ univ.image (markedRow F.triad s) := by
    rintro h
    obtain ⟨i, _, he⟩ := mem_image.mp h
    exact short_ne_markedRow F s hs U (fun j => hU (mem_image.mpr ⟨j, mem_univ _, rfl⟩)) i he.symm
  have hsx : x ∈ univ.image s ↔ x = s j := by
    constructor
    · intro h
      obtain ⟨i, _, hi⟩ := mem_image.mp h
      have hij : i = j := by
        by_contra hne
        exact disjoint_left.mp (F.pairwise_disjoint hne) (hs i) (hi ▸ hxj)
      simpa [hij] using hi.symm
    · intro h
      exact mem_image.mpr ⟨j, mem_univ _, h.symm⟩
  have hxU : x ∈ U ↔ x = s j := by
    constructor
    · intro h
      apply hsx.mp
      by_contra hn
      exact hxA (hA ▸ mem_sdiff.mpr ⟨h, hn⟩)
    · intro h
      exact hU (hsx.mpr h)
  have hd := triad_marked_degree F s hs hxj
  have hdi : degree (insert U (univ.image (markedRow F.triad s))) x =
      (if x ∈ U then 1 else 0) + degree (univ.image (markedRow F.triad s)) x := by
    by_cases hx : x ∈ U
    · simp [degree, star, filter_insert, hx, hUnot, Nat.add_comm]
    · simp [degree, star, filter_insert, hx]
  rw [hdi, hd]
  by_cases hxs : x = s j
  · have hx : x ∈ U := hxU.mpr hxs
    rw [ite_eq_left hx, ite_eq_left hxs]
  · have hx : x ∉ U := fun h => hxs (hxU.mp h)
    rw [ite_eq_right hx, ite_eq_right hxs]

/- The three common rows contribute exactly one incidence outside the root. -/
omit hs in
theorem common_rows_degree_one {x : α} (hx : x ∉ K) :
    degree (univ.image fun j => K ∪ F.triad j) x = 1 := by
  have hu : x ∈ K ∪ univ.biUnion F.triad := by rw [F.spans]; exact mem_univ _
  obtain ⟨j, _, hxj⟩ := mem_biUnion.mp ((mem_union.mp hu).resolve_left hx)
  rw [degree_image_of_injective _ F.marked_injective]
  have hf : (univ.filter fun i => x ∈ K ∪ F.triad i) = {j} := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union, hx, false_or, mem_singleton]
    constructor
    · intro hxi
      by_contra hne
      exact disjoint_left.mp (F.pairwise_disjoint hne) hxi hxj
    · rintro rfl
      exact hxj
  rw [hf, card_singleton]

/- Six disjoint edge families with degree two each, together with the three
common rows, have degree thirteen at every indicated outside point. -/
omit hs in
theorem degree_thirteen_of_six_families (P : Fin 6 → Family α)
    (hP : Pairwise fun i j => Disjoint (P i) (P j))
    (hcommon : ∀ i, Disjoint (univ.image fun j => K ∪ F.triad j) (P i))
    {x : α} (hx : x ∉ K) (hdegree : ∀ i, degree (P i) x = 2) :
    degree ((univ.image fun j => K ∪ F.triad j) ∪ univ.biUnion P) x = 13 := by
  have hd : Disjoint (univ.image fun j => K ∪ F.triad j) (univ.biUnion P) := by
    apply disjoint_left.mpr
    intro B hB hBP
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hBP
    exact disjoint_left.mp (hcommon i) hB hi
  rw [degree_union_of_disjoint hd, common_rows_degree_one F hx,
    degree_biUnion_of_pairwise P hP]
  simp [hdegree]

end Triads

#guard_standard_axioms degree_union_of_disjoint degree_image_of_injective
  degree_biUnion_of_pairwise degree_union_image_of_disjoint
  triad_markedRow_injective triad_marked_degree trace_family_degree_two
  common_rows_degree_one degree_thirteen_of_six_families

end CoveringDesigns.C13Structural
