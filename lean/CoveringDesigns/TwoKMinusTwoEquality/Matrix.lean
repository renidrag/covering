import CoveringDesigns.BoundaryRank.Equality

/-! Square representative incidence matrices at boundary equality.
The parameter equation follows from invertibility and the two margins.
Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusTwoEquality
open Finset Matrix Module
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
/-- Nonnegative constant matrices are positive semidefinite. -/
theorem constant_posSemidef (lam : ℝ) (hlam : 0 ≤ lam) :
    (Matrix.of (fun (_ _ : ι) => lam)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp
  · intro x
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply]
    have he : (∑ i, x i * ∑ j, lam * x j) = lam * (∑ i, x i)^2 := by
      rw [← mul_sum, ← sum_mul]
      ring
    rw [he]
    positivity

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- Equal square-Gram rows are the same actual real row. -/
theorem rows_eq_of_gram (R : Matrix ι κ ℝ) (i j : ι) (r : ℝ)
    (hi : (R * R.transpose) i i = r)
    (hj : (R * R.transpose) j j = r)
    (hij : (R * R.transpose) i j = r) :
    ∀ x, R i x = R j x := by
  have hs : (∑ x, (R i x - R j x)^2) = 0 := by
    have he : (∑ x, (R i x - R j x)^2) =
        (R * R.transpose) i i + (R * R.transpose) j j -
          2 * (R * R.transpose) i j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      rw [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro x _
      ring
    rw [he, hi, hj, hij]
    ring
  intro x
  have hx := (sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (R i x - R j x))).mp hs x (mem_univ _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- A square matrix with row sum r and Gram (r-lam)I+lamJ has the same column
sum and the symmetric-design parameter equation. No binary assumption is
needed once the Gram identity is supplied. Nonempty columns are explicit. -/
theorem square_parameters (M : Matrix κ κ ℝ) (r lam : ℝ)
    (hlam : 0 ≤ lam) (hlt : lam < r) (hb : 0 < Fintype.card κ)
    (hrow : ∀ i, ∑ j, M i j = r)
    (hgram : M * M.transpose =
      Matrix.diagonal (fun _ => r-lam) + Matrix.of (fun _ _ => lam)) :
    (∀ j, ∑ i, M i j = r) ∧ lam * ((Fintype.card κ : ℝ)-1) = r*(r-1) := by
  have hr : 0 < r := lt_of_le_of_lt hlam hlt
  have hpd : (M * M.transpose).PosDef := by
    rw [hgram]
    exact (Matrix.PosDef.diagonal (fun _ => sub_pos.mpr hlt)).add_posSemidef
      (constant_posSemidef lam hlam)
  have hdet : M.det ≠ 0 := by
    intro hz
    have hp := hpd.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, hz] at hp
    norm_num at hp
  have hinj := Matrix.mulVec_injective_of_det_ne_zero hdet
  let q : ℝ := (r-lam+lam*(Fintype.card κ : ℝ))/r
  have hq : q*r = r-lam+lam*(Fintype.card κ : ℝ) := by
    dsimp [q]
    exact div_mul_cancel₀ _ (ne_of_gt hr)
  have hcolvec : M.transpose *ᵥ (fun _ => (1 : ℝ)) = fun _ => q := by
    apply hinj
    rw [Matrix.mulVec_mulVec, hgram, Matrix.add_mulVec]
    funext i
    simp only [Pi.add_apply, Matrix.mulVec_diagonal, mul_one]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_one, sum_const,
      card_univ, nsmul_eq_mul]
    rw [← sum_mul, hrow]
    linarith
  have hcol (j : κ) : ∑ i, M i j = q := by
    simpa [Matrix.mulVec, dotProduct] using congr_fun hcolvec j
  have hsum : (Fintype.card κ : ℝ)*r = (Fintype.card κ : ℝ)*q := by
    calc
      (Fintype.card κ : ℝ)*r = ∑ i, ∑ j, M i j := by simp [hrow]
      _ = ∑ j, ∑ i, M i j := sum_comm
      _ = (Fintype.card κ : ℝ)*q := by simp [hcol]
  have hbR : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have heq : r=q := mul_left_cancel₀ hbR hsum
  refine ⟨fun j => (hcol j).trans heq.symm, ?_⟩
  rw [← heq] at hq
  nlinarith

/-- The reviewed equality argument: component pairs, equal actual supports,
and a square representative Gram matrix force the parameter equation. -/
theorem boundary_parameter (R : Matrix ι κ ℝ) (r lam : ℝ)
    (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hlam : 0 ≤ lam) (hlt : lam < r) (hb : 0 < Fintype.card κ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hz : ∀ i, E i i = 0) (hδ : ∀ i, 0 ≤ δ i)
    (hbalance : ∀ i, (∑ j, E i j) + δ i = r-lam)
    (hrow : ∀ i, ∑ j, R i j = r)
    (hgram : R * R.transpose =
      Matrix.diagonal (fun _ => r-lam) + E + Matrix.of (fun _ _ => lam))
    (hcard : Fintype.card ι = 2 * Fintype.card κ) :
    (∀ i, δ i = 0) ∧
    (∃ e : κ × Bool ≃ ι,
      (∀ i j, R (e (i,false)) j = R (e (i,true)) j) ∧
      (∀ i j, i ≠ j → (R * R.transpose) (e (i,false)) (e (j,false)) = lam)) ∧
    lam * ((Fintype.card κ : ℝ)-1) = r*(r-1) := by
  obtain ⟨hd,e,hcross,hweight⟩ := BoundaryRank.gram_equality R (r-lam) E δ
    (sub_pos.mpr hlt) hs hn hz hδ hbalance
    (Matrix.of (fun _ _ => lam)) (constant_posSemidef lam hlam) hgram hcard
  have hself (i : ι) : (R * R.transpose) i i = r := by
    rw [hgram]
    simp [hz]
  have hpaired (i : κ) : (R * R.transpose) (e (i,false)) (e (i,true)) = r := by
    have hne : e (i,false) ≠ e (i,true) := by
      intro h
      have hh := e.injective h
      cases hh
    rw [hgram]
    simp [hne, hweight]
  have hroweq (i : κ) (j : κ) : R (e (i,false)) j = R (e (i,true)) j :=
    rows_eq_of_gram R _ _ r (hself _) (hself _) (hpaired i) j
  have hother (i j : κ) (hij : i ≠ j) :
      (R * R.transpose) (e (i,false)) (e (j,false)) = lam := by
    have hne : e (i,false) ≠ e (j,false) := by
      intro h
      exact hij (congr_arg Prod.fst (e.injective h))
    rw [hgram]
    simp [hne, hcross i j hij false false]
  let M : Matrix κ κ ℝ := fun i j => R (e (i,false)) j
  have hMrow (i : κ) : ∑ j, M i j = r := hrow _
  have hMgram : M * M.transpose =
      Matrix.diagonal (fun _ => r-lam) + Matrix.of (fun _ _ => lam) := by
    ext i j
    have he : (M * M.transpose) i j =
        (R * R.transpose) (e (i,false)) (e (j,false)) := rfl
    rw [he]
    by_cases hij : i=j
    · subst j
      simp [hself]
    · simp [hij, hother i j hij]
  exact ⟨hd, ⟨e,hroweq,hother⟩, (square_parameters M r lam hlam hlt hb hMrow hMgram).2⟩

end CoveringDesigns.TwoKMinusTwoEquality
