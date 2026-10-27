import CoveringDesigns.TwistedArithmetic.Determinant
import CoveringDesigns.PairEquality.Twisted

/-! The historical order-four determinant obstruction, on actual incidences. -/
namespace CoveringDesigns.TwistedArithmetic
open Finset Matrix PairEquality
variable {I : Type*} [Fintype I] [DecidableEq I] {H : Finset (Finset I)} {q : ℕ}

/-- Integer incidence with coordinates as rows and actual occupied supports as columns. -/
def incidence (H : Finset (Finset I)) : Matrix I H ℤ := fun x E => if x ∈ E.val then 1 else 0

theorem incidence_gram (T : IsTwistedPlane q H) (x y : I) :
    (incidence H * (incidence H).transpose) x y =
      (if x = y then (q : ℤ) else 0) + 1 + (if y = T.coordinateMate x then 1 else 0) := by
  have he : (incidence H * (incidence H).transpose) x y = (codegree H x y : ℤ) := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply,incidence]
    rw [sum_coe_sort H (fun E => (if x ∈ E then (1 : ℤ) else 0) * (if y ∈ E then 1 else 0))]
    simp only [codegree,card_eq_sum_ones,sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    apply sum_congr rfl
    intro E hE
    split_ifs <;> simp_all
  rw [he]
  by_cases hxy : x = y
  · subst y
    have hc : codegree H x x = q+1 := by simpa [codegree,PairEquality.degree] using T.degree_eq x
    simp [hc,T.coordinateMate_ne x,Ne.symm (T.coordinateMate_ne x)]
  · rw [T.coordinate_codegree x y hxy]
    split_ifs <;> simp_all

noncomputable def squareIncidence (T : IsTwistedPlane q H) : Matrix I I ℤ :=
  (incidence H).submatrix id (Fintype.equivOfCardEq (by simpa using T.coordinates.trans T.supports.symm))

private theorem square_gram (T : IsTwistedPlane q H) :
    squareIncidence T * (squareIncidence T).transpose = incidence H * (incidence H).transpose := by
  ext x y
  simp only [squareIncidence,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix_apply,id_eq]
  exact Equiv.sum_comp _ (fun E : H => incidence H x E * incidence H y E)

/-- The Gram determinant is derived from the verified mate involution and codegrees. -/
theorem order_four_determinant (T : IsTwistedPlane 4 H) :
    (squareIncidence T).det ^ 2 = (3 : ℤ)^10 * 5^11 := by
  classical
  let f := T.coordinateMate
  let e := mateEquiv f T.coordinateMate_involutive T.coordinateMate_ne
  have hc : Fintype.card (MateRepresentatives f) = 10 := by
    have he := mateRepresentatives_card f T.coordinateMate_involutive T.coordinateMate_ne
    rw [T.coordinates] at he
    omega
  let G := incidence H * (incidence H).transpose
  have he : ((G.map (fun z : ℤ => (z : ℚ))).submatrix e e) = pairedGram (R := MateRepresentatives f) 4 := by
    have entry (x y : MateRepresentatives f ⊕ MateRepresentatives f) :
        ((G.map (fun z : ℤ => (z : ℚ))).submatrix e e) x y =
          (if x = y then (4 : ℚ) else 0) + 1 + (if y = x.swap then 1 else 0) := by
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
  rw [Matrix.det_submatrix_equiv_self,← Int.cast_det,pairedGram_det 4 (by norm_num),hc] at hd
  have hg : G.det = (3 : ℤ)^10 * 5^11 := by
    exact_mod_cast (by norm_num at hd ⊢; exact hd : (G.det : ℚ) = (3 : ℚ)^10 * 5^11)
  have hs := congrArg Matrix.det (square_gram T)
  rw [Matrix.det_mul,Matrix.det_transpose] at hs
  simpa only [pow_two] using hs.trans hg

private theorem not_integer_square (d : ℤ) : d^2 ≠ (3 : ℤ)^10 * 5^11 := by
  intro h
  have he : |d|^2 = (2883251953125 : ℤ) := by simpa using h
  have hp : 0 ≤ |d| := abs_nonneg d
  by_cases hb : |d| ≤ 1698014
  · nlinarith
  · have hb' : 1698015 ≤ |d| := by omega
    nlinarith

/-- No actual twisted plane of order four exists. -/
theorem no_twisted_four (T : IsTwistedPlane 4 H) : False :=
  not_integer_square (squareIncidence T).det (order_four_determinant T)

end CoveringDesigns.TwistedArithmetic
