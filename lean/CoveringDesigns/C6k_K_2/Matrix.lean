import CoveringDesigns.C6k_K_2.Isotropic
import CoveringDesigns.C6k_K_2.PrimeKernel

/-! The order-six obstruction for arbitrary integer incidence-shaped matrices. -/

open Matrix Module
open scoped BigOperators

namespace CoveringDesigns.C6k_K_2

private theorem row_rank_le {L T : Type*} [Fintype L] [Nonempty L] [Fintype T]
    (hT : Fintype.card T = 43) (M : Matrix L T (ZMod 3))
    (hrow : ∀ l, ∑ t, M l t = 1)
    (hgram : M * M.transpose = Matrix.of (fun (_ _ : L) => (1 : ZMod 3))) :
    M.rank ≤ 21 := by
  classical
  let R := LinearMap.range M.vecMulLinear
  have hsum (c : L → ZMod 3) : coordinateSum (c ᵥ* M) = ∑ l, c l := by
    change (∑ t, ∑ l, c l * M l t) = _
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hrow, mul_one]
  have hpair (x : T → ZMod 3) (hx : x ∈ R) (y : T → ZMod 3) (hy : y ∈ R) :
      x ⬝ᵥ y = coordinateSum x * coordinateSum y := by
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    change (c ᵥ* M) ⬝ᵥ (d ᵥ* M) = coordinateSum (c ᵥ* M) * coordinateSum (d ᵥ* M)
    rw [hsum, hsum, ← dotProduct_mulVec, mulVec_vecMul, hgram]
    simp [mulVec, dotProduct, Finset.sum_mul]
  let s : R →ₗ[ZMod 3] ZMod 3 := coordinateSum.domRestrict R
  let l : L := Classical.arbitrary L
  have hmem : M l ∈ R := by
    refine ⟨Pi.single l 1, ?_⟩
    ext t
    simp [Matrix.vecMul, single_dotProduct]
  let r : R := ⟨M l, hmem⟩
  have hsr : s r = 1 := hrow l
  have hsur : Function.Surjective s := by
    intro a
    refine ⟨a • r, ?_⟩
    rw [map_smul, hsr, smul_eq_mul, mul_one]
  let K := LinearMap.ker s
  let W := K.map R.subtype
  have hWR : W ≤ R := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hWsum : ∀ x ∈ W, ∑ t, x t = 0 := by
    rintro x ⟨y, hy, rfl⟩
    exact hy
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, x ⬝ᵥ y = 0 := by
    intro x hx y hy
    rw [hpair x (hWR hx) y (hWR hy)]
    change (∑ t, x t) * (∑ t, y t) = 0
    rw [hWsum x hx, zero_mul]
  have hWdim := sum_zero_isotropic_finrank_le hT W hWsum hWiso
  have hnull := s.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsur, finrank_top, Module.finrank_self] at hnull
  have hW : Module.finrank (ZMod 3) W = Module.finrank (ZMod 3) K :=
    Submodule.finrank_map_subtype_eq R K
  have hR : M.rank = Module.finrank (ZMod 3) R := by
    change M.rank = Module.finrank (ZMod 3) (LinearMap.range M.vecMulLinear)
    rw [M.rank_eq_finrank_span_row, range_vecMulLinear]
  change 1 + Module.finrank (ZMod 3) K = Module.finrank (ZMod 3) R at hnull
  rw [← hW, ← hR] at hnull
  omega

/-- No integer matrix on 43 lines and 43 points has row sums seven and both
order-six Gram identities. No restriction on individual entries is assumed. -/
theorem no_order_six_matrix {L T : Type*} [Fintype L] [Fintype T]
    [DecidableEq L] [DecidableEq T]
    (hL : Fintype.card L = 43) (hT : Fintype.card T = 43)
    (A : Matrix L T ℤ) (hrow : ∀ l, ∑ t, A l t = 7)
    (hrows : A * A.transpose = (6 : ℤ) • 1 + Matrix.of (fun (_ _ : L) => (1 : ℤ)))
    (hcols : A.transpose * A = (6 : ℤ) • 1 + Matrix.of (fun (_ _ : T) => (1 : ℤ))) :
    False := by
  classical
  let : Nonempty L := Fintype.card_pos_iff.mp (by omega)
  let f := Int.castRingHom (ZMod 3)
  let M := A.map f
  have hrowM : ∀ l, ∑ t, M l t = 1 := by
    intro l
    have h := congrArg f (hrow l)
    simpa [M, f, map_sum, show (7 : ZMod 3) = 1 from by decide] using h
  have hgramM : M * M.transpose = Matrix.of (fun (_ _ : L) => (1 : ZMod 3)) := by
    ext i j
    have h := congrArg (fun B : Matrix L L ℤ => f (B i j)) hrows
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Matrix.of_apply] at h
    by_cases hij : i = j <;>
      simpa [M, f, Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
        hij, map_sum, show (6 : ZMod 3) = 0 from by decide,
        show (7 : ZMod 3) = 1 from by decide] using h
  have hu := row_rank_le hT M hrowM hgramM
  have hk : 2 * Module.finrank (ZMod 3) (LinearMap.ker M.mulVecLin) ≤ Fintype.card T := by
    apply isotropic_finrank_le
    intro x hx y hy
    exact kernel_totally_isotropic (p := 3) (a := 2) A (by decide) (by simpa using hcols)
      x y hx hy
  have hn := M.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, hT] at hn
  change M.rank + Module.finrank (ZMod 3) (LinearMap.ker M.mulVecLin) = 43 at hn
  omega

end CoveringDesigns.C6k_K_2
