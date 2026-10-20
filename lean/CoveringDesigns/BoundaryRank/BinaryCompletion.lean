import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Binary completion at column corank at most two

For a real matrix annihilating the all-ones vector, fixing both the matrix
image and the coordinate sum removes one dimension from its kernel. At
column corank at most two, a binary fibre consequently has at most two
distinct vectors. At corank at most one, every such fibre is a singleton
or empty, even without the binary restriction.

Formalisation: Rob Gardiner with AI assistance.
-/

namespace CoveringDesigns.BoundaryRank

open Finset Matrix Module

variable {ι κ X : Type*} [Fintype ι] [Fintype κ]

private def coordinateSum : (κ → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ j, x j
  map_add' x y := by simp [sum_add_distrib]
  map_smul' c x := by simp [mul_sum]

private def zeroSumKernel (T : Matrix ι κ ℝ) : Submodule ℝ (κ → ℝ) :=
  LinearMap.ker T.mulVecLin ⊓ LinearMap.ker coordinateSum

omit [Fintype ι] in
private theorem zeroSumKernel_finrank_lt (T : Matrix ι κ ℝ)
    (hT : T *ᵥ (fun _ => 1) = 0) (hb : 0 < Fintype.card κ) :
    finrank ℝ (zeroSumKernel T) < finrank ℝ (LinearMap.ker T.mulVecLin) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_iff_le_and_ne.mpr ⟨inf_le_left, ?_⟩
  intro heq
  have hm : (fun _ : κ => (1 : ℝ)) ∈ zeroSumKernel T := by
    rw [heq]
    exact hT
  have hz : (Fintype.card κ : ℝ) = 0 := by
    simpa [coordinateSum] using hm.2
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)) hz

private theorem zeroSumKernel_finrank_le (T : Matrix ι κ ℝ)
    (hT : T *ᵥ (fun _ => 1) = 0) (hb : 0 < Fintype.card κ)
    {d : ℕ} (hcorank : Fintype.card κ - T.rank ≤ d + 1) :
    finrank ℝ (zeroSumKernel T) ≤ d := by
  have hlt := zeroSumKernel_finrank_lt T hT hb
  have htotal : T.rank + finrank ℝ (LinearMap.ker T.mulVecLin) =
      Fintype.card κ := by
    simpa [Matrix.rank] using T.mulVecLin.finrank_range_add_finrank_ker
  omega

omit [Fintype ι] in
private theorem sub_mem_zeroSumKernel (T : Matrix ι κ ℝ) {x y : κ → ℝ}
    (himage : T *ᵥ x = T *ᵥ y) (hsum : (∑ j, x j) = ∑ j, y j) :
    x - y ∈ zeroSumKernel T := by
  constructor
  · change T *ᵥ (x - y) = 0
    rw [Matrix.mulVec_sub, himage, sub_self]
  · change (∑ j, (x - y) j) = 0
    simpa only [Pi.sub_apply, sum_sub_distrib, sub_eq_zero] using hsum

/-- At positive width and column corank at most one, prescribing the image
under a matrix annihilating the all-ones vector and the coordinate sum
determines the vector uniquely. Binary entries are not needed. -/
theorem completion_eq_of_corank_le_one (T : Matrix ι κ ℝ)
    (hT : T *ᵥ (fun _ => 1) = 0) (hb : 0 < Fintype.card κ)
    (hcorank : Fintype.card κ - T.rank ≤ 1)
    {x y : κ → ℝ} (himage : T *ᵥ x = T *ᵥ y)
    (hsum : (∑ j, x j) = ∑ j, y j) : x = y := by
  have hdim : finrank ℝ (zeroSumKernel T) = 0 := by
    have hh := zeroSumKernel_finrank_le T hT hb (d := 0) hcorank
    omega
  have hz := finrank_zero_iff_forall_zero.mp hdim
    (⟨x - y, sub_mem_zeroSumKernel T himage hsum⟩ : zeroSumKernel T)
  have heq : x - y = 0 := congr_arg Subtype.val hz
  exact sub_eq_zero.mp heq

/-- Every binary completion is one of any two distinct binary completions,
provided the matrix is centered and has column corank at most two.
The indexing family may repeat a support arbitrarily many times. -/
theorem binary_completion_eq_or_eq (T : Matrix ι κ ℝ)
    (hT : T *ᵥ (fun _ => 1) = 0) (hb : 0 < Fintype.card κ)
    (hcorank : Fintype.card κ - T.rank ≤ 2)
    (w : X → κ → ℝ) (hbinary : ∀ x j, w x j = 0 ∨ w x j = 1)
    (a : ι → ℝ) (himage : ∀ x, T *ᵥ w x = a)
    (h : ℝ) (hsum : ∀ x, (∑ j, w x j) = h)
    {x₀ x₁ : X} (hne : w x₀ ≠ w x₁) (x : X) :
    w x = w x₀ ∨ w x = w x₁ := by
  classical
  let u : zeroSumKernel T :=
    ⟨w x₁ - w x₀, sub_mem_zeroSumKernel T
      ((himage x₁).trans (himage x₀).symm) ((hsum x₁).trans (hsum x₀).symm)⟩
  have hu : u ≠ 0 := by
    intro hu
    have hv : w x₁ - w x₀ = 0 := congr_arg Subtype.val hu
    exact hne (sub_eq_zero.mp hv).symm
  have hdim : finrank ℝ (zeroSumKernel T) = 1 := by
    have hle := zeroSumKernel_finrank_le T hT hb (d := 1) hcorank
    have hnz : finrank ℝ (zeroSumKernel T) ≠ 0 := by
      intro hz
      exact hu (finrank_zero_iff_forall_zero.mp hz u)
    omega
  let v : zeroSumKernel T :=
    ⟨w x - w x₀, sub_mem_zeroSumKernel T
      ((himage x).trans (himage x₀).symm) ((hsum x).trans (hsum x₀).symm)⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hu v
  have hcval : c • (w x₁ - w x₀) = w x - w x₀ := congr_arg Subtype.val hc
  obtain ⟨j, hj⟩ : ∃ j, w x₀ j ≠ w x₁ j := Function.ne_iff.mp hne
  have hcj : c * (w x₁ j - w x₀ j) = w x j - w x₀ j := congr_fun hcval j
  have hc01 : c = 0 ∨ c = 1 := by
    rcases hbinary x₀ j with h₀ | h₀ <;>
      rcases hbinary x₁ j with h₁ | h₁ <;>
      rcases hbinary x j with hx | hx <;>
      simp_all
  rcases hc01 with rfl | rfl
  · left
    simpa only [zero_smul, eq_comm, sub_eq_zero] using hcval
  · right
    have heq : w x₁ - w x₀ = w x - w x₀ := by simpa only [one_smul] using hcval
    exact (sub_left_inj.mp heq).symm

/-- A finite binary family with fixed image and fixed coordinate sum has at
most two distinct support vectors under the centered corank-two hypothesis. -/
theorem binary_completion_card_le_two [Fintype X] (T : Matrix ι κ ℝ)
    (hT : T *ᵥ (fun _ => 1) = 0) (hb : 0 < Fintype.card κ)
    (hcorank : Fintype.card κ - T.rank ≤ 2)
    (w : X → κ → ℝ) (hbinary : ∀ x j, w x j = 0 ∨ w x j = 1)
    (a : ι → ℝ) (himage : ∀ x, T *ᵥ w x = a)
    (h : ℝ) (hsum : ∀ x, (∑ j, w x j) = h) :
    (univ.image w).card ≤ 2 := by
  classical
  by_cases hcard : (univ.image w).card ≤ 1
  · omega
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hcard)
    obtain ⟨x₀, _, rfl⟩ := mem_image.mp hu
    obtain ⟨x₁, _, rfl⟩ := mem_image.mp hv
    have hsub : univ.image w ⊆ {w x₀, w x₁} := by
      intro z hz
      obtain ⟨x, _, rfl⟩ := mem_image.mp hz
      simpa only [mem_insert, mem_singleton] using
        binary_completion_eq_or_eq T hT hb hcorank w hbinary a himage h hsum huv x
    exact (card_le_card hsub).trans Finset.card_le_two

/-- The corank-one analogue counts distinct support vectors, allowing any
number of repeated occurrences in the indexing family. -/
theorem completion_card_le_one [Fintype X] (T : Matrix ι κ ℝ)
    (hT : T *ᵥ (fun _ => 1) = 0) (hb : 0 < Fintype.card κ)
    (hcorank : Fintype.card κ - T.rank ≤ 1)
    (w : X → κ → ℝ) (a : ι → ℝ) (himage : ∀ x, T *ᵥ w x = a)
    (h : ℝ) (hsum : ∀ x, (∑ j, w x j) = h) :
    (univ.image w).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨x, _, rfl⟩ := mem_image.mp hu
  obtain ⟨y, _, rfl⟩ := mem_image.mp hv
  exact completion_eq_of_corank_le_one T hT hb hcorank
    ((himage x).trans (himage y).symm) ((hsum x).trans (hsum y).symm)

end CoveringDesigns.BoundaryRank
