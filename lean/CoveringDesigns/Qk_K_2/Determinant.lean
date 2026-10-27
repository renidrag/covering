import CoveringDesigns.TwistedArithmetic.OrderFour

/-! General determinant-to-exclusion interface, reusing the verified actual
Gram matrix and paired determinant. No construction or numerical application. -/
namespace CoveringDesigns.Qk_K_2
open Finset Matrix PairEquality TwistedArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I] {H : Finset (Finset I)} {q : ℕ}

/-- The historical integer square obstruction for an actual twisted plane. -/
theorem twisted_determinant (hq : 1 ≤ q) (T : IsTwistedPlane q H) :
    (squareIncidence T).det ^ 2 =
      ((q-1 : ℕ) : ℤ)^(q*(q+1)/2) * (q+1 : ℕ)^(q*(q+1)/2+1) := by
  classical
  let f := T.coordinateMate
  let e := mateEquiv f T.coordinateMate_involutive T.coordinateMate_ne
  have hc : Fintype.card (MateRepresentatives f) = q*(q+1)/2 := by
    have he := mateRepresentatives_card f T.coordinateMate_involutive T.coordinateMate_ne
    rw [T.coordinates] at he
    omega
  let G := incidence H * (incidence H).transpose
  have he : ((G.map (fun z : ℤ => (z : ℚ))).submatrix e e) = pairedGram (R := MateRepresentatives f) q := by
    have entry (x y : MateRepresentatives f ⊕ MateRepresentatives f) :
        ((G.map (fun z : ℤ => (z : ℚ))).submatrix e e) x y =
          (if x = y then (q : ℚ) else 0) + 1 + (if y = x.swap then 1 else 0) := by
      have hm : e y = T.coordinateMate (e x) ↔ y = x.swap := by
        have hh := mateEquiv_swap f T.coordinateMate_involutive T.coordinateMate_ne x
        change e x.swap = T.coordinateMate (e x) at hh
        rw [← hh]
        exact e.injective.eq_iff
      change (((incidence H * (incidence H).transpose) (e x) (e y) : ℤ) : ℚ) = _
      rw [incidence_gram T]
      simp [e.injective.eq_iff,hm]
    ext x y
    rw [entry,pairedGram_apply]
  have hd := congrArg Matrix.det he
  rw [Matrix.det_submatrix_equiv_self,← Int.cast_det,pairedGram_det (q : ℚ) (by positivity),hc] at hd
  have hpair := mateRepresentatives_card f T.coordinateMate_involutive T.coordinateMate_ne
  rw [T.coordinates,hc] at hpair
  have hpair' : (2 : ℚ)*(q*(q+1)/2 : ℕ) = (q : ℚ)*(q+1) := by exact_mod_cast hpair
  have hratio : (1 : ℚ) + 2*(q*(q+1)/2 : ℕ)/((q : ℚ)+1) = (q : ℚ)+1 := by
    field_simp
    nlinarith
  have hsub : ((q-1 : ℕ) : ℚ) = (q : ℚ)-1 := by
    rw [Nat.cast_sub hq, Nat.cast_one]
  have hg : G.det = ((q-1 : ℕ) : ℤ)^(q*(q+1)/2) * (q+1 : ℕ)^(q*(q+1)/2+1) := by
    rw [hratio] at hd
    have hg' : (G.det : ℚ) = ((q-1 : ℕ) : ℚ)^(q*(q+1)/2) *
        ((q+1 : ℕ) : ℚ)^(q*(q+1)/2+1) := by
      simpa only [hsub,Nat.cast_add,Nat.cast_one,pow_succ,mul_assoc] using hd
    exact_mod_cast hg'
  have hs : squareIncidence T * (squareIncidence T).transpose = G := by
    ext x y
    simp only [squareIncidence,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix_apply,id_eq]
    exact Equiv.sum_comp _ (fun E : H => incidence H x E * incidence H y E)
  have hh := congrArg Matrix.det hs
  rw [Matrix.det_mul,Matrix.det_transpose] at hh
  simpa only [pow_two] using hh.trans hg

/-- A kernel-proved nonsquare excludes the actual geometry. -/
theorem exclude_twisted (hq : 1 ≤ q)
    (hn : ∀ d : ℤ, d^2 ≠ ((q-1 : ℕ) : ℤ)^(q*(q+1)/2) * (q+1 : ℕ)^(q*(q+1)/2+1))
    (T : IsTwistedPlane q H) : False :=
  hn _ (twisted_determinant hq T)

end CoveringDesigns.Qk_K_2
