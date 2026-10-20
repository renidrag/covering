import CoveringDesigns.AffineCapacity.Cube
import CoveringDesigns.BoundaryRank.Completion
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Prescribed-image fibres at arbitrary column corank

The full real fibre is a translate of a sum-zero kernel of dimension
`corank - 1`. Binary counting and affine covering capacity are separate
consequences. These public helpers leave `BinaryCompletion` unchanged.
-/

namespace CoveringDesigns.SupportDimension

open Finset Module Matrix AffineCapacity

variable {ι κ α : Type*} [Fintype ι] [Fintype κ]

/-- Coordinate sum as a real linear functional. -/
def coordinateSum : (κ → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ i, w i
  map_add' x y := by simp [sum_add_distrib]
  map_smul' c x := by simp [mul_sum]

/-- Directions preserving both image and degree. -/
def zeroSumKernel (T : Matrix ι κ ℝ) : Submodule ℝ (κ → ℝ) :=
  LinearMap.ker T.mulVecLin ⊓ LinearMap.ker coordinateSum

/-- Positive width and centering force positive column corank. -/
theorem one_le_corank (T : Matrix ι κ ℝ) (hb : 0 < Fintype.card κ)
    (hT : T *ᵥ (fun _ => (1 : ℝ)) = 0) :
    1 ≤ Fintype.card κ - T.rank :=
  BoundaryRank.one_le_corank_of_mulVec_one_eq_zero T hb hT

/-- Fixing degree removes exactly one dimension from the centered kernel. -/
theorem zeroSumKernel_finrank (T : Matrix ι κ ℝ)
    (hb : 0 < Fintype.card κ) (hT : T *ᵥ (fun _ => (1 : ℝ)) = 0) :
    finrank ℝ (zeroSumKernel T) = Fintype.card κ - T.rank - 1 := by
  let K := LinearMap.ker T.mulVecLin
  let f : K →ₗ[ℝ] ℝ := coordinateSum.comp K.subtype
  have hf : f ≠ 0 := by
    intro hf
    have he := LinearMap.congr_fun hf (⟨fun _ => (1 : ℝ), hT⟩ : K)
    have hz : (Fintype.card κ : ℝ) = 0 := by
      simpa [f, coordinateSum] using he
    exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)) hz
  have heq : LinearMap.ker f = (zeroSumKernel T).comap K.subtype := by
    ext z
    simp [f, zeroSumKernel, K]
  have hdim : finrank ℝ (LinearMap.ker f) = finrank ℝ (zeroSumKernel T) := by
    rw [heq]
    exact (Submodule.comapSubtypeEquivOfLe
      (show zeroSumKernel T ≤ K from inf_le_left)).finrank_eq
  have hdrop := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [hdim] at hdrop
  have htotal : T.rank + finrank ℝ K = Fintype.card κ := by
    simpa [Matrix.rank, K] using T.mulVecLin.finrank_range_add_finrank_ker
  omega

/-- Equal images and sums give a direction in the sum-zero kernel. -/
theorem sub_mem_zeroSumKernel (T : Matrix ι κ ℝ) {x y : κ → ℝ}
    (himage : T *ᵥ x = T *ᵥ y) (hsum : (∑ i, x i) = ∑ i, y i) :
    x - y ∈ zeroSumKernel T := by
  constructor
  · change T *ᵥ (x - y) = 0
    rw [Matrix.mulVec_sub, himage, sub_self]
  · change (∑ i, (x - y) i) = 0
    simpa only [Pi.sub_apply, sum_sub_distrib, sub_eq_zero] using hsum

/-- A supplied real solution identifies the entire fibre as a translate.
No binary assumption or centering is needed for this set identity. -/
theorem fibre_eq_translate (T : Matrix ι κ ℝ) (a : ι → ℝ) (h : ℝ)
    (w₀ : κ → ℝ) (ha : T *ᵥ w₀ = a) (hh : (∑ i, w₀ i) = h) :
    {w | T *ᵥ w = a ∧ (∑ i, w i) = h} =
      (AffineSubspace.mk' w₀ (zeroSumKernel T) : Set (κ → ℝ)) := by
  ext w
  change (T *ᵥ w = a ∧ (∑ i, w i) = h) ↔ w - w₀ ∈ zeroSumKernel T
  constructor
  · rintro ⟨hw, hs⟩
    exact sub_mem_zeroSumKernel T (hw.trans ha.symm) (hs.trans hh.symm)
  · rintro ⟨hm, hs⟩
    change T *ᵥ (w - w₀) = 0 at hm
    rw [Matrix.mulVec_sub, ha, sub_eq_zero] at hm
    change (∑ i, (w - w₀) i) = 0 at hs
    simp only [Pi.sub_apply, sum_sub_distrib, hh, sub_eq_zero] at hs
    exact ⟨hm, hs⟩

/-- Exact affine dimension of a nonempty full real fibre. Binary
nonemptiness is not asserted by the supplied real solution. -/
theorem fibre_dimension (T : Matrix ι κ ℝ) (hb : 0 < Fintype.card κ)
    (hT : T *ᵥ (fun _ => (1 : ℝ)) = 0)
    (a : ι → ℝ) (h : ℝ) (w₀ : κ → ℝ)
    (ha : T *ᵥ w₀ = a) (hh : (∑ i, w₀ i) = h) :
    dimension {w | T *ᵥ w = a ∧ (∑ i, w i) = h} =
      Fintype.card κ - T.rank - 1 := by
  rw [fibre_eq_translate T a h w₀ ha hh]
  unfold dimension
  rw [← direction_affineSpan, AffineSubspace.affineSpan_coe,
    AffineSubspace.direction_mk', zeroSumKernel_finrank T hb hT]

/-- Actual selected rows have at most the fibre dimension. Empty
selections are included, with affine dimension zero. -/
theorem family_dimension_le (T : Matrix ι κ ℝ)
    (hb : 0 < Fintype.card κ) (hT : T *ᵥ (fun _ => (1 : ℝ)) = 0)
    (F : Finset α) (w : α → κ → ℝ) (a : ι → ℝ) (h : ℝ)
    (ha : ∀ x ∈ F, T *ᵥ w x = a) (hh : ∀ x ∈ F, (∑ i, w x i) = h) :
    dimension (w '' (F : Set α)) ≤ Fintype.card κ - T.rank - 1 := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · unfold dimension
    rw [Finset.coe_empty, Set.image_empty, vectorSpan_empty, finrank_bot]
    omega
  have hsub : affineSpan ℝ (w '' (F : Set α)) ≤
      AffineSubspace.mk' (w x₀) (zeroSumKernel T) := by
    apply affineSpan_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact sub_mem_zeroSumKernel T ((ha x hx).trans (ha x₀ hx₀).symm)
      ((hh x hx).trans (hh x₀ hx₀).symm)
  have hd := Submodule.finrank_mono (AffineSubspace.direction_le hsub)
  rw [direction_affineSpan, AffineSubspace.direction_mk',
    zeroSumKernel_finrank T hb hT] at hd
  exact hd

/-- Arbitrary-corank bound on distinct binary supports, not actual points. -/
theorem binary_support_card_le (T : Matrix ι κ ℝ)
    (hb : 0 < Fintype.card κ) (hT : T *ᵥ (fun _ => (1 : ℝ)) = 0)
    (F : Finset α) (w : α → κ → ℝ)
    (hbin : ∀ x ∈ F, ∀ i, w x i = 0 ∨ w x i = 1)
    (a : ι → ℝ) (h : ℝ)
    (ha : ∀ x ∈ F, T *ᵥ w x = a) (hh : ∀ x ∈ F, (∑ i, w x i) = h) :
    (F.image w).card ≤ 2 ^ (Fintype.card κ - T.rank - 1) := by
  classical
  rw [← zeroSumKernel_finrank T hb hT]
  apply binary_card_le_pow (zeroSumKernel T)
  · rintro _ hz i
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    exact hbin x hx i
  · rintro _ hz _ hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hv
    exact sub_mem_zeroSumKernel T ((ha x hx).trans (ha y hy).symm)
      ((hh x hx).trans (hh y hy).symm)

/-- Covering capacity for actual points with a common image and degree. -/
theorem common_block [Fintype α] [DecidableEq α]
    (B : κ → Finset α) (F : Finset α) (hF : F.Nonempty)
    (T : Matrix ι κ ℝ) (hb : 0 < Fintype.card κ)
    (hT : T *ᵥ (fun _ => (1 : ℝ)) = 0) {t : ℕ}
    (ht : 1 ≤ t) (htv : t ≤ Fintype.card α)
    (hcover : ∀ U : Finset α, U.card = t → ∃ i, U ⊆ B i)
    (hu : Fintype.card κ - T.rank ≤ t)
    (a : ι → ℝ) (h : ℝ)
    (ha : ∀ x ∈ F, T *ᵥ row B x = a)
    (hh : ∀ x ∈ F, (∑ i, row B x i) = h) :
    ∃ i, F ⊆ B i := by
  apply exists_block_of_dimension_lt B F hF ht htv hcover
  have hd := family_dimension_le T hb hT F (row B) a h ha hh
  have hp := one_le_corank T hb hT
  omega

end CoveringDesigns.SupportDimension
