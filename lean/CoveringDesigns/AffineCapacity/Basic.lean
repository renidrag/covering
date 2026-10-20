import CoveringDesigns.Foundations.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Actual affine representatives and covering capacity

Affine dimension is the dimension of the vector space of differences, not
the linear rank of the rows. Representatives are selected from actual points.
Equal rows do not identify points; equal blocks do not identify occurrences.
Formalisation: Rob Gardiner with AI assistance.
-/

namespace CoveringDesigns.AffineCapacity

open Finset Module

variable {α ι : Type*} [Fintype ι]

/-- Real affine dimension, with the usual zero-dimensional convention for
the empty set. Nonempty hypotheses are stated separately when needed. -/
noncomputable def dimension (s : Set (ι → ℝ)) : ℕ :=
  finrank ℝ (vectorSpan ℝ s)

/-- Select an affine basis among actual points, without requiring the row
map to be injective. The selected point set has exactly `d+1` members. -/
theorem exists_spanning_points (F : Finset α) (hF : F.Nonempty)
    (w : α → ι → ℝ) :
    ∃ S : Finset α, S ⊆ F ∧
      S.card = dimension (w '' (F : Set α)) + 1 ∧
      affineSpan ℝ (w '' (S : Set α)) = affineSpan ℝ (w '' (F : Set α)) := by
  classical
  obtain ⟨t, ht, hspan, hind⟩ :=
    exists_affineIndependent ℝ (ι → ℝ) (w '' (F : Set α))
  have hfinite : t.Finite := (F.finite_toSet.image w).subset ht
  have hne : t.Nonempty := by
    by_contra hn
    have he : t = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨x, hx⟩ := hF
    have hm := mem_affineSpan ℝ (Set.mem_image_of_mem w hx)
    rw [← hspan, he] at hm
    exact (show w x ∈ (⊥ : AffineSubspace ℝ (ι → ℝ)) by simpa using hm)
  let := hfinite.fintype
  let : Nonempty t := hne.to_subtype
  have hd : vectorSpan ℝ t = vectorSpan ℝ (w '' (F : Set α)) := by
    simpa only [direction_affineSpan] using congrArg AffineSubspace.direction hspan
  have hc : hfinite.toFinset.card = dimension (w '' (F : Set α)) + 1 := by
    have hh := hind.finrank_vectorSpan_add_one
    have hrt : Set.range (Subtype.val : t → (ι → ℝ)) = t := by ext z; simp
    rw [hrt, hd] at hh
    simpa only [dimension, Set.Finite.card_toFinset] using hh.symm
  obtain ⟨S, hS, hinj, himg⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (F : Set α) hfinite.toFinset
      (by
        intro z hz
        exact ht (by simpa using hz))
  refine ⟨S, hS, ?_, ?_⟩
  · rw [← Finset.card_image_of_injOn hinj, himg, hc]
  · have he : w '' (S : Set α) = t := by
      simpa only [← Finset.coe_image, himg, Set.Finite.coe_toFinset]
    rw [he, hspan]

omit [Fintype ι] in
/-- A coordinate constant on generators is constant on their affine span.
Coefficients need not be nonnegative. -/
theorem coordinate_eq_of_mem_affineSpan {s : Set (ι → ℝ)} {z : ι → ℝ}
    (hz : z ∈ affineSpan ℝ s) (i : ι) (c : ℝ)
    (hs : ∀ w ∈ s, w i = c) : z i = c := by
  refine affineSpan_induction hz hs ?_
  intro a x y z hx hy hz
  change a * (x i - y i) + z i = c
  rw [hx, hy, hz]
  ring

/-- Actual binary incidence rows for indexed blocks. -/
def row [DecidableEq α] (B : ι → Finset α) (x : α) : ι → ℝ :=
  fun i => if x ∈ B i then 1 else 0

omit [Fintype ι] in
@[simp] theorem row_eq_one_iff [DecidableEq α] (B : ι → Finset α)
    (x : α) (i : ι) : row B x i = 1 ↔ x ∈ B i := by
  simp [row]

/-- Any actual affine-spanning selection determines exactly the common
block indices. This statement needs no covering or block-size premise. -/
theorem common_support_eq [DecidableEq α] (B : ι → Finset α)
    (F S : Finset α) (hS : S ⊆ F)
    (hspan : affineSpan ℝ (row B '' (S : Set α)) =
      affineSpan ℝ (row B '' (F : Set α))) :
    {i | ∀ x ∈ F, x ∈ B i} = {i | ∀ x ∈ S, x ∈ B i} := by
  ext i
  constructor
  · exact fun h x hx => h x (hS hx)
  · intro h x hx
    apply (row_eq_one_iff B x i).mp
    apply coordinate_eq_of_mem_affineSpan (i := i) (c := 1)
    · rw [hspan]
      exact mem_affineSpan ℝ (Set.mem_image_of_mem (row B) hx)
    · rintro _ ⟨y, hy, rfl⟩
      exact (row_eq_one_iff B y i).mpr (h y hy)

/-- Affine dimension below covering strength forces one actual block.
No uniformity, distinct-block or injective-row premise is imposed. -/
theorem exists_block_of_dimension_lt [Fintype α] [DecidableEq α]
    (B : ι → Finset α) (F : Finset α) {t : ℕ}
    (hF : F.Nonempty) (_ht : 1 ≤ t) (htv : t ≤ Fintype.card α)
    (hcover : ∀ U : Finset α, U.card = t → ∃ i, U ⊆ B i)
    (hd : dimension (row B '' (F : Set α)) < t) :
    ∃ i, F ⊆ B i := by
  obtain ⟨S, hS, hcard, hspan⟩ := exists_spanning_points F hF (row B)
  obtain ⟨U, hSU, _, hU⟩ := Finset.exists_subsuperset_card_eq
    (subset_univ S) (show S.card ≤ t by omega) (by simpa using htv)
  obtain ⟨i, hi⟩ := hcover U hU
  have hcommon := common_support_eq B F S hS hspan
  have hm : i ∈ {j | ∀ x ∈ S, x ∈ B j} := fun x hx => hi (hSU hx)
  rw [← hcommon] at hm
  exact ⟨i, hm⟩

/-- Separate cardinality interface, including empty point selections. -/
theorem card_le_of_dimension_lt [Fintype α] [DecidableEq α]
    (B : ι → Finset α) (F : Finset α) {t k : ℕ}
    (ht : 1 ≤ t) (htv : t ≤ Fintype.card α)
    (hcover : ∀ U : Finset α, U.card = t → ∃ i, U ⊆ B i)
    (hsize : ∀ i, (B i).card ≤ k)
    (hd : dimension (row B '' (F : Set α)) < t) : F.card ≤ k := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  obtain ⟨i, hi⟩ := exists_block_of_dimension_lt B F hF ht htv hcover hd
  exact (card_le_card hi).trans (hsize i)

end CoveringDesigns.AffineCapacity
