import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! The fixed 42-dimensional discriminant obstruction over `ZMod 3`. -/

open Matrix Module

namespace CoveringDesigns.C6k_K_2

private theorem swap_det {n : Type*} [Fintype n] [DecidableEq n] :
    (fromBlocks (0 : Matrix n n (ZMod 3)) (1 : Matrix n n (ZMod 3)) 1 0).det =
      (-1 : ZMod 3) ^ Fintype.card n := by
  have hf : fromBlocks (0 : Matrix n n (ZMod 3)) (1 : Matrix n n (ZMod 3))
      (1 : Matrix n n (ZMod 3)) (0 : Matrix n n (ZMod 3)) =
      fromBlocks (1 : Matrix n n (ZMod 3)) (1 : Matrix n n (ZMod 3))
        (1 : Matrix n n (ZMod 3)) (0 : Matrix n n (ZMod 3)) *
      fromBlocks (1 : Matrix n n (ZMod 3)) (0 : Matrix n n (ZMod 3))
        (-1 : Matrix n n (ZMod 3)) (1 : Matrix n n (ZMod 3)) := by
    simp [fromBlocks_multiply]
  rw [hf, det_mul, det_fromBlocks_one₁₁, det_fromBlocks_zero₁₂]
  simp [det_neg]

private theorem zero_block_det (B D : Matrix (Fin 21) (Fin 21) (ZMod 3)) :
    (fromBlocks 0 B B.transpose D).det = -(B.det ^ 2) := by
  have hm : fromBlocks (0 : Matrix (Fin 21) (Fin 21) (ZMod 3)) 1 1 0 *
      fromBlocks 0 B B.transpose D = fromBlocks B.transpose D 0 B := by
    simp [fromBlocks_multiply]
  have hd := congrArg Matrix.det hm
  rw [det_mul, swap_det, det_fromBlocks_zero₂₁, det_transpose] at hd
  norm_num at hd
  linear_combination -hd

private theorem adapted_det
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (U : Submodule (ZMod 3) V)
    (bU : Basis (Fin 21) (ZMod 3) U)
    (bQ : Basis (Fin 21) (ZMod 3) (V ⧸ U))
    (Q : LinearMap.BilinForm (ZMod 3) V) (hsym : Q.IsSymm)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, Q x y = 0) :
    ∃ d : ZMod 3, (Q.toMatrix (bU.sumQuot bQ)).det = -(d ^ 2) := by
  classical
  let c := bU.sumQuot bQ
  let B : Matrix (Fin 21) (Fin 21) (ZMod 3) :=
    fun i j => Q (c (Sum.inl i)) (c (Sum.inr j))
  let D : Matrix (Fin 21) (Fin 21) (ZMod 3) :=
    fun i j => Q (c (Sum.inr i)) (c (Sum.inr j))
  have hblocks : Q.toMatrix c = fromBlocks 0 B B.transpose D := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change Q (bU.sumQuot bQ (Sum.inl i)) (bU.sumQuot bQ (Sum.inl j)) = 0
        rw [Basis.sumQuot_inl, Basis.sumQuot_inl]
        exact hiso (bU i) (bU i).property (bU j) (bU j).property
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => exact hsym.eq _ _
      | inr j => rfl
  refine ⟨B.det, ?_⟩
  change (Q.toMatrix c).det = _
  rw [hblocks, zero_block_det]

/-- A determinant-one symmetric form on `F₃⁴²` has no totally isotropic
21-dimensional subspace. The adapted basis is constructed from the submodule. -/
theorem no_isotropic_half
    (U : Submodule (ZMod 3) (Fin 42 → ZMod 3))
    (G : Matrix (Fin 42) (Fin 42) (ZMod 3))
    (hsym : G.IsSymm) (hdet : G.det = 1)
    (hdim : Module.finrank (ZMod 3) U = 21)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ (G *ᵥ y) = 0) : False := by
  classical
  have hquot : Module.finrank (ZMod 3) ((Fin 42 → ZMod 3) ⧸ U) = 21 := by
    have h := U.finrank_quotient_add_finrank
    simp only [hdim, Module.finrank_pi, Fintype.card_fin] at h
    omega
  let bU := Module.finBasisOfFinrankEq (ZMod 3) U hdim
  let bQ := Module.finBasisOfFinrankEq (ZMod 3) ((Fin 42 → ZMod 3) ⧸ U) hquot
  let c := bU.sumQuot bQ
  let e : Fin 21 ⊕ Fin 21 ≃ Fin 42 := finSumFinEquiv
  let b := (Pi.basisFun (ZMod 3) (Fin 42)).reindex e.symm
  let Q := G.toBilin'
  have hbase : Q.toMatrix b = G.submatrix e e := by
    ext i j
    simp [b, Q, Basis.reindex_apply, Pi.basisFun_apply, Matrix.toBilin'_single]
  have hbase_det : (Q.toMatrix b).det = 1 := by
    rw [hbase, Matrix.det_submatrix_equiv_self, hdet]
  have hc : (b.toMatrix c).det ≠ 0 := by
    rw [← Basis.det_apply]
    exact (b.isUnit_det c).ne_zero
  have hc_square : (b.toMatrix c).det ^ 2 = 1 :=
    (by decide : ∀ z : ZMod 3, z ≠ 0 → z ^ 2 = 1) _ hc
  have hchange : (Q.toMatrix c).det = 1 := by
    rw [← Q.toMatrix_mul_basis_toMatrix b c, det_mul, det_mul, det_transpose]
    calc
      (b.toMatrix c).det * (Q.toMatrix b).det * (b.toMatrix c).det =
          (b.toMatrix c).det ^ 2 * (Q.toMatrix b).det := by ring
      _ = 1 := by rw [hc_square, hbase_det, one_mul]
  have hsymQ : Q.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hsym
  have hisoQ : ∀ x ∈ U, ∀ y ∈ U, Q x y = 0 := by
    simpa only [Q, Matrix.toBilin'_apply'] using hiso
  obtain ⟨d, hd⟩ := adapted_det U bU bQ Q hsymQ hisoQ
  exact (by decide : ∀ z : ZMod 3, -(z ^ 2) ≠ 1) d (hd.symm.trans hchange)

end CoveringDesigns.C6k_K_2
