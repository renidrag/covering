import CoveringDesigns.C6k_K_2.Discriminant
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Dimension bounds for the two isotropic subspaces in the order-six proof. -/

open Matrix Module
open scoped BigOperators

namespace CoveringDesigns.C6k_K_2

/-- A totally isotropic subspace for the standard dot product has at most
half the ambient dimension, over any field. -/
theorem isotropic_finrank_le {K T : Type*} [Field K] [Fintype T]
    (U : Submodule K (T → K))
    (hiso : ∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ y = 0) :
    2 * Module.finrank K U ≤ Fintype.card T := by
  classical
  let b := Module.finBasis K U
  let N : Matrix (Fin (Module.finrank K U)) T K := fun i => b i
  have hli : LinearIndependent K N := b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hzero : N * N.transpose = 0 := by
    ext i j
    exact hiso (b i) (b i).property (b j) (b j).property
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  rw [Matrix.rank_transpose, hli.rank_matrix, Fintype.card_fin] at h
  omega

def coordinateSum {K T : Type*} [Field K] [Fintype T] : (T → K) →ₗ[K] K where
  toFun x := ∑ t, x t
  map_add' x y := Finset.sum_add_distrib
  map_smul' c x := by simp [Finset.mul_sum]

private noncomputable def sumZeroChart {K : Type*} [Field K] {n : ℕ} :
    (Fin n → K) ≃ₗ[K] LinearMap.ker (coordinateSum (K := K) (T := Fin (n+1))) where
  toFun z := ⟨Fin.lastCases (-∑ i, z i) z, by
    change (∑ i : Fin (n+1), Fin.lastCases (-∑ j, z j) z i) = (0 : K)
    rw [Fin.sum_univ_castSucc]
    simp⟩
  invFun x i := x.val i.castSucc
  left_inv z := by funext i; simp
  right_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h := x.property
      change (∑ i, x.val i) = 0 at h
      rw [Fin.sum_univ_castSucc] at h
      simpa using (eq_neg_of_add_eq_zero_right h).symm
    · simp
  map_add' z w := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Finset.sum_add_distrib, add_comm]
  map_smul' a z := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Finset.mul_sum]

private theorem sumZeroChart_pairing {K : Type*} [Field K] {n : ℕ} (z w : Fin n → K) :
    (sumZeroChart z).val ⬝ᵥ (sumZeroChart w).val =
      z ⬝ᵥ (((1 : Matrix (Fin n) (Fin n) K) +
        Matrix.of (fun _ _ => 1)) *ᵥ w) := by
  rw [add_mulVec, one_mulVec, dotProduct_add]
  change (∑ i : Fin (n+1), (Fin.lastCases (-∑ j, z j) z i : K) *
    (Fin.lastCases (-∑ j, w j) w i : K)) = _
  rw [Fin.sum_univ_castSucc]
  simp [dotProduct, mulVec, Finset.sum_mul]

private theorem sum_zero_gram_det :
    ((1 : Matrix (Fin 42) (Fin 42) (ZMod 3)) +
      Matrix.of (fun (_ _ : Fin 42) => (1 : ZMod 3))).det = 1 := by
  have he : Matrix.of (fun (_ _ : Fin 42) => (1 : ZMod 3)) =
      replicateCol Unit (fun _ : Fin 42 => (1 : ZMod 3)) *
      replicateRow Unit (fun _ : Fin 42 => (1 : ZMod 3)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [he, det_one_add_replicateCol_mul_replicateRow]
  norm_num [dotProduct]
  decide

private theorem sum_zero_finrank_fin43
    (U : Submodule (ZMod 3) (Fin 43 → ZMod 3))
    (hsum : ∀ x ∈ U, ∑ i, x i = 0)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ y = 0) : Module.finrank (ZMod 3) U ≤ 20 := by
  have hbound := isotropic_finrank_le U hiso
  simp only [Fintype.card_fin] at hbound
  by_contra h
  have hdim : Module.finrank (ZMod 3) U = 21 := by omega
  let V := LinearMap.ker (coordinateSum (K := ZMod 3) (T := Fin 43))
  have hUV : U ≤ V := fun x hx => hsum x hx
  let W := U.comap V.subtype
  let W' := W.map (sumZeroChart (K := ZMod 3) (n := 42)).symm.toLinearMap
  have hdim' : Module.finrank (ZMod 3) W' = 21 := by
    rw [LinearEquiv.finrank_map_eq]
    exact (Submodule.comapSubtypeEquivOfLe hUV).finrank_eq.trans hdim
  apply no_isotropic_half W' (1 + Matrix.of (fun _ _ => 1))
    (by ext i j; simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm])
    sum_zero_gram_det hdim'
  intro z hz w hw
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hw
  rw [← sumZeroChart_pairing]
  simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hiso x hx y hy

/-- In 43 coordinates over `F₃`, isotropy together with coordinate sum zero
improves the usual half-dimension bound to 20. -/
theorem sum_zero_isotropic_finrank_le {T : Type*} [Fintype T]
    (hT : Fintype.card T = 43) (U : Submodule (ZMod 3) (T → ZMod 3))
    (hsum : ∀ x ∈ U, ∑ i, x i = 0)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ y = 0) : Module.finrank (ZMod 3) U ≤ 20 := by
  classical
  let e : T ≃ Fin 43 := Fintype.equivFinOfCardEq hT
  let f := LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) e.symm
  rw [← f.finrank_map_eq U]
  apply sum_zero_finrank_fin43 (U.map f.toLinearMap)
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact (e.symm.sum_comp z).trans (hsum z hz)
  · intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact (e.symm.sum_comp (fun t => z t * w t)).trans (hiso z hz w hw)

end CoveringDesigns.C6k_K_2
