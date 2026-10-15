import CoveringDesigns.Foundations.BinaryCap
import CoveringDesigns.C12_6_3.Structural.Templates
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
The twelve underlying projective hyperplanes in the no-duplicate branch.
All covering-dependent assertions below are counting and relabelling
arguments. The fixed coordinate identities concern only `F₂⁴`.
-/

namespace CoveringDesigns.GPPTProjectiveTemplate

open Finset BinaryCap

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def projectiveKernel (n : V) : Finset V :=
  univ.filter (fun v => v ≠ 0 ∧ dot n v = 0)

def normalRow (n : Fin 12 → V) (v : V) : Finset (Fin 12) :=
  univ.filter (fun p => dot (n p) v = 0)

theorem projectiveKernel_card :
    ∀ n : V, n ≠ 0 → (projectiveKernel n).card = 7 := by
  decide +kernel

theorem projectiveKernel_inter_card :
    ∀ a b : V, a ≠ 0 → b ≠ 0 → a ≠ b →
      (projectiveKernel a ∩ projectiveKernel b).card = 3 := by
  decide +kernel

theorem dot_comm (a b : V) : dot a b = dot b a := by
  unfold dot
  apply sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- Count the incidences in seven rows by their twelve point columns. -/
theorem kernel_row_sum (n : Fin 12 → V) (a : V) :
    ∑ v ∈ projectiveKernel a, (normalRow n v).card =
      ∑ p, (projectiveKernel a ∩ projectiveKernel (n p)).card := by
  simp only [normalRow, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have he : (projectiveKernel a).filter (fun v => dot (n p) v = 0) =
      projectiveKernel a ∩ projectiveKernel (n p) := by
    ext v
    simp only [projectiveKernel, mem_filter, mem_univ, true_and, mem_inter]
    tauto
  rw [← he]
  simp only [sum_filter]

/-- Repeated normals would force more than six core incidences in a row. -/
theorem normal_injective (n : Fin 12 → V) (hn : ∀ p, n p ≠ 0)
    (hrow : ∀ v, v ≠ 0 → (normalRow n v).card ≤ 6) : Function.Injective n := by
  have hmult (a : V) (ha : a ≠ 0) : (univ.filter (fun p => n p = a)).card ≤ 1 := by
    have hbound : (∑ v ∈ projectiveKernel a, (normalRow n v).card) ≤ 42 := by
      calc
        _ ≤ ∑ _v ∈ projectiveKernel a, 6 := sum_le_sum fun v hv =>
          hrow v (mem_filter.mp hv).2.1
        _ = 42 := by simp [projectiveKernel_card a ha]
    rw [kernel_row_sum] at hbound
    have hval (p : Fin 12) :
        (projectiveKernel a ∩ projectiveKernel (n p)).card =
          3 + if n p = a then 4 else 0 := by
      by_cases hp : n p = a
      · simp [hp, projectiveKernel_card a ha]
      · simp [hp, projectiveKernel_inter_card a (n p) ha (hn p) (Ne.symm hp)]
    simp_rw [hval] at hbound
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      sum_ite, sum_const] at hbound
    omega
  intro p q hpq
  have hm := hmult (n p) (hn p)
  have hp : p ∈ univ.filter (fun x => n x = n p) := by simp
  have hq : q ∈ univ.filter (fun x => n x = n p) := by simp [hpq]
  exact (card_le_one.mp hm) p hp q hq

/-- The normals omitted by the twelve point columns. -/
def omitted (n : Fin 12 → V) : Finset V :=
  (univ.erase 0) \ univ.image n

theorem omitted_card (n : Fin 12 → V) (hn : ∀ p, n p ≠ 0)
    (hinj : Function.Injective n) : (omitted n).card = 3 := by
  have hs : univ.image n ⊆ (univ : Finset V).erase 0 := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := mem_image.mp hv
    exact mem_erase.mpr ⟨hn p, mem_univ _⟩
  rw [omitted, card_sdiff_of_subset hs, card_image_of_injective _ hinj]
  have hc : ((univ : Finset V).erase 0).card = 15 := by decide +kernel
  simp [hc]

/-- Every row hyperplane contains one of the three omitted normals. -/
theorem omitted_meets_kernel (n : Fin 12 → V) (hn : ∀ p, n p ≠ 0)
    (hrow : ∀ v, v ≠ 0 → (normalRow n v).card ≤ 6)
    (v : V) (hv : v ≠ 0) : ∃ a ∈ omitted n, dot a v = 0 := by
  by_contra h
  push Not at h
  have hi := normal_injective n hn hrow
  have hs : projectiveKernel v ⊆ (normalRow n v).image n := by
    intro a ha
    obtain ⟨ha0, hav⟩ := (mem_filter.mp ha).2
    have hav' := (dot_comm a v).trans hav
    have haN : a ∈ univ.image n := by
      by_contra hnA
      exact h a (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ha0, mem_univ _⟩, hnA⟩) hav'
    obtain ⟨p, _, hp⟩ := mem_image.mp haN
    refine mem_image.mpr ⟨p, ?_, hp⟩
    exact mem_filter.mpr ⟨mem_univ _, hp ▸ hav'⟩
  have hc := card_le_card hs
  rw [projectiveKernel_card v hv, card_image_of_injective _ hi] at hc
  have hb := hrow v hv
  omega

theorem omitted_is_line (n : Fin 12 → V) (hn : ∀ p, n p ≠ 0)
    (hrow : ∀ v, v ≠ 0 → (normalRow n v).card ≤ 6) :
    ∃ a b : V, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ omitted n = {a, b, a + b} := by
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := card_eq_three.mp
    (omitted_card n hn (normal_injective n hn hrow))
  have hz (x : V) (hx : x ∈ omitted n) : x ≠ 0 :=
    (mem_erase.mp (mem_sdiff.mp hx).1).1
  have ha : a ≠ 0 := hz a (by simp [he])
  have hb : b ≠ 0 := hz b (by simp [he])
  have hc : c ≠ 0 := hz c (by simp [he])
  have hs := three_point_blocking_collinear a b c ha hb hc hab hac hbc (by
    intro v hv
    obtain ⟨x, hx, hd⟩ := omitted_meets_kernel n hn hrow v hv
    rw [he] at hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl ((dot_comm v _).trans hd)
    · exact Or.inr (Or.inl ((dot_comm v _).trans hd))
    · exact Or.inr (Or.inr ((dot_comm v _).trans hd)))
  have hsum : a + b = c := by
    funext i
    exact CharTwo.add_eq_zero.mp (congrFun hs i)
  exact ⟨a, b, ha, hb, hab, by simpa only [hsum] using he⟩

/-- The fixed dual line omitted in the standard Figure 1 coordinates. -/
def standardLine : Finset V :=
  {Pi.single 0 1, Pi.single 1 1, Pi.single 0 1 + Pi.single 1 1}

/-- Four normals in each of the three nonzero cosets of the omitted line. -/
def standardNormal : Fin 12 → V := ![
  ![0, 0, 1, 0], ![0, 1, 1, 0], ![1, 0, 1, 0], ![1, 1, 1, 0],
  ![0, 0, 0, 1], ![0, 1, 0, 1], ![1, 0, 0, 1], ![1, 1, 0, 1],
  ![0, 0, 1, 1], ![0, 1, 1, 1], ![1, 0, 1, 1], ![1, 1, 1, 1]]

def coreFamily (n : Fin 12 → V) : Family (Fin 12) :=
  (univ.erase (0 : V)).image (normalRow n)

theorem standardNormal_injective : Function.Injective standardNormal := by decide +kernel

theorem standardNormal_image :
    univ.image standardNormal = (univ.erase 0) \ standardLine := by decide +kernel

/-- One fixed incidence table: projective space with the standard dual line
deleted is precisely the partial covering in GPPT Figure 1. -/
theorem standard_coreFamily : coreFamily standardNormal = figure1 := by decide +kernel

private def dotLinearLeft (v : V) : V →ₗ[ZMod 2] ZMod 2 where
  toFun x := dot x v
  map_add' x y := by simp [dot, add_mul, sum_add_distrib]
  map_smul' k x := by simp [dot, mul_assoc, mul_sum]

/-- A change of coordinates on normal vectors induces a change of row
coordinates by the dual linear map. -/
theorem exists_dual_row (e : V ≃ₗ[ZMod 2] V) (v : V) (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ ∀ x, dot (e x) v = dot x w := by
  let f := (dotLinearLeft v).comp e.toLinearMap
  let w : V := fun i => f (Pi.single i 1)
  have he (x : V) : dot (e x) v = dot x w :=
    (linear_eq_dot f x).trans (dot_comm w x)
  refine ⟨w, ?_, he⟩
  intro hw
  apply hv
  funext i
  have hh := he (e.symm (Pi.single i 1))
  rw [e.apply_symm_apply, hw] at hh
  have hs : dot (Pi.single i 1) v = v i := by
    unfold dot
    rw [sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  rw [hs] at hh
  simpa [dot] using hh

private theorem coreFamily_linear_subset (e : V ≃ₗ[ZMod 2] V) (n : Fin 12 → V) :
    coreFamily (fun p => e (n p)) ⊆ coreFamily n := by
  intro B hB
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hB
  obtain ⟨w, hw, he⟩ := exists_dual_row e v (mem_erase.mp hv).1
  refine mem_image.mpr ⟨w, mem_erase.mpr ⟨hw, mem_univ _⟩, ?_⟩
  ext p
  simp only [normalRow, mem_filter, mem_univ, true_and, he]

theorem coreFamily_linear (e : V ≃ₗ[ZMod 2] V) (n : Fin 12 → V) :
    coreFamily (fun p => e (n p)) = coreFamily n := by
  apply Subset.antisymm (coreFamily_linear_subset e n)
  simpa only [e.symm_apply_apply] using
    coreFamily_linear_subset e.symm (fun p => e (n p))

theorem relabel_coreFamily (e : Equiv.Perm (Fin 12)) (n : Fin 12 → V) :
    relabel e (coreFamily n) = coreFamily (fun p => n (e.symm p)) := by
  unfold coreFamily
  unfold relabel
  rw [map_eq_image, image_image]
  change (univ.erase (0 : V)).image (fun v => (normalRow n v).map e.toEmbedding) = _
  congr 1
  funext v
  ext p
  simp only [mem_map_equiv, normalRow, mem_filter, mem_univ, true_and]

/-- Normalize the omitted line, then identify the twelve remaining normal
vectors with the twelve points of the fixed Figure 1 table. -/
theorem coreFamily_isomorphic_figure1 (n : Fin 12 → V) (hn : ∀ p, n p ≠ 0)
    (hrow : ∀ v, v ≠ 0 → (normalRow n v).card ≤ 6) :
    Isomorphic (coreFamily n) figure1 := by
  classical
  obtain ⟨a, b, ha, hb, hab, hline⟩ := omitted_is_line n hn hrow
  obtain ⟨e, hea, heb⟩ := pair_normalize a b ha hb hab
  have hm : (omitted n).map e.toEquiv.toEmbedding = standardLine := by
    simp only [hline, map_insert, map_singleton, LinearEquiv.coe_toEquiv,
      Equiv.coe_toEmbedding, map_add, hea, heb, standardLine]
  have hmem (p : Fin 12) : e (n p) ∈ univ.image standardNormal := by
    rw [standardNormal_image]
    apply mem_sdiff.mpr
    constructor
    · exact mem_erase.mpr ⟨fun h => hn p (e.injective (h.trans e.map_zero.symm)), mem_univ _⟩
    · intro hs
      rw [← hm] at hs
      have hp : n p ∈ omitted n := (mem_map' e.toEquiv.toEmbedding).mp hs
      exact (mem_sdiff.mp hp).2 (mem_image.mpr ⟨p, mem_univ _, rfl⟩)
  have hchoose : ∀ p, ∃ q, standardNormal q = e (n p) := by
    intro p
    obtain ⟨q, _, hq⟩ := mem_image.mp (hmem p)
    exact ⟨q, hq⟩
  choose f hf using hchoose
  have hfi : Function.Injective f := by
    intro p q hpq
    apply normal_injective n hn hrow
    apply e.injective
    rw [← hf p, ← hf q, hpq]
  let ep : Equiv.Perm (Fin 12) :=
    Equiv.ofBijective f ⟨hfi, Finite.surjective_of_injective hfi⟩
  refine ⟨ep, ?_⟩
  calc
    relabel ep (coreFamily n) = relabel ep (coreFamily (fun p => e (n p))) :=
      congrArg (relabel ep) (coreFamily_linear e n).symm
    _ = coreFamily (fun p => e (n (ep.symm p))) := relabel_coreFamily ep _
    _ = coreFamily standardNormal := by
      congr 1
      funext p
      have hh := hf (ep.symm p)
      change standardNormal (ep (ep.symm p)) = e (n (ep.symm p)) at hh
      simpa only [ep.apply_symm_apply] using hh.symm
    _ = figure1 := standard_coreFamily

open GPPTStructural

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
/-- Enlarging the three four-point rows is the only way to extend Figure 1
inside a family of at most fifteen six-point blocks. -/
theorem templateCompletion_of_partial_extension (C : Family (Fin 12))
    (hu : Uniform C 6) (hc : C.card ≤ 15)
    (hext : ∀ A ∈ figure1, ∃ B ∈ C, A ⊆ B) : IsTemplateCompletion C := by
  classical
  have hcore : core ⊆ C := by
    intro A hA
    obtain ⟨B, hB, hAB⟩ := hext A (mem_filter.mp hA).1
    have he : A = B := eq_of_subset_of_card_le hAB (by
      rw [hu B hB, core_uniform A hA])
    exact he ▸ hB
  have hsp (i : Fin 3) : spine i ∈ figure1 := by
    exact (show ∀ i, spine i ∈ figure1 by decide +kernel) i
  have hchoose : ∀ i, ∃ B ∈ C, spine i ⊆ B := fun i => hext _ (hsp i)
  choose B hBC hsub using hchoose
  have hBi : Function.Injective B := by
    intro i j hij
    by_contra hne
    have hs : spine i ∪ spine j ⊆ B j := union_subset (hij ▸ hsub i) (hsub j)
    have hb := card_le_card hs
    have hcard : (spine i ∪ spine j).card = 8 :=
      (show ∀ i j : Fin 3, i ≠ j → (spine i ∪ spine j).card = 8 by decide +kernel) i j hne
    rw [hcard, hu _ (hBC j)] at hb
    omega
  have hd : Disjoint core (univ.image B) := by
    apply disjoint_left.mpr
    intro A hA hAB
    obtain ⟨i, _, rfl⟩ := mem_image.mp hAB
    have hn : ¬ spine i ⊆ B i :=
      (show ∀ i, ∀ A ∈ core, ¬ spine i ⊆ A by decide +kernel) i (B i) hA
    exact hn (hsub i)
  have hfamily : C = core ∪ univ.image B := by
    symm
    apply eq_of_subset_of_card_le
    · apply union_subset hcore
      intro A hA
      obtain ⟨i, _, rfl⟩ := mem_image.mp hA
      exact hBC i
    · rw [card_union_of_disjoint hd, core_card, card_image_of_injective _ hBi]
      exact hc
  exact (isTemplateCompletion_iff_extensions C).mpr
    ⟨B, fun i => ⟨hsub i, hu _ (hBC i)⟩, hfamily⟩

/-- Every covering whose block rows extend these twelve normal hyperplanes
is isomorphic to a completion of GPPT Figure 1. -/
theorem isomorphic_completion_of_normal_cores (C : Family (Fin 12))
    (hu : Uniform C 6) (hc : C.card ≤ 15)
    (n : Fin 12 → V) (hn : ∀ p, n p ≠ 0)
    (hext : ∀ v, v ≠ 0 → ∃ B ∈ C, normalRow n v ⊆ B) :
    IsomorphicTemplateCompletion C := by
  have hrow (v : V) (hv : v ≠ 0) : (normalRow n v).card ≤ 6 := by
    obtain ⟨B, hB, hs⟩ := hext v hv
    exact (card_le_card hs).trans_eq (hu B hB)
  obtain ⟨e, he⟩ := coreFamily_isomorphic_figure1 n hn hrow
  refine ⟨relabel e C, ?_, ⟨e, rfl⟩⟩
  apply templateCompletion_of_partial_extension _ (relabel_uniform e hu)
    (by simpa only [relabel_card] using hc)
  intro A hA
  rw [← he] at hA
  obtain ⟨D, hD, rfl⟩ := mem_map.mp hA
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hD
  obtain ⟨B, hB, hs⟩ := hext v (mem_erase.mp hv).1
  exact ⟨B.map e.toEmbedding, (mem_relabel e C B).mpr hB, map_subset_map.mpr hs⟩

#guard_standard_axioms projectiveKernel_card projectiveKernel_inter_card
  normal_injective omitted_card omitted_meets_kernel omitted_is_line
  standard_coreFamily coreFamily_isomorphic_figure1 templateCompletion_of_partial_extension
  isomorphic_completion_of_normal_cores

end CoveringDesigns.GPPTProjectiveTemplate
