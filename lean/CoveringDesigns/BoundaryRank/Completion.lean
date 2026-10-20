import CoveringDesigns.BoundaryRank.Nullity

/-!
# Centering and a quantitative rank budget at the signless boundary

Constant row sums allow centering without rank loss when the remaining
constant Gram term is nonnegative. The existing component-coordinate nullity
bound also controls the number of positive deficits. Empty row types are
allowed throughout. Formalisation: Rob Gardiner with AI assistance.
-/

namespace CoveringDesigns.BoundaryRank

open Finset Matrix Module

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Subtract the common row average from every entry. -/
noncomputable def centered (R : Matrix ι κ ℝ) (r : ℝ) : Matrix ι κ ℝ :=
  R - Matrix.of (fun _ _ => r / (Fintype.card κ : ℝ))

/-- A signless kernel vector at a positive constant diagonal has sum zero. -/
theorem kernel_sum_zero (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hδ : ∀ i, 0 ≤ δ i)
    (hrow : ∀ i, (∑ j, E i j) + δ i = ρ)
    {x : ι → ℝ} (hx : (Matrix.diagonal (fun _ => ρ) + E) *ᵥ x = 0) :
    ∑ i, x i = 0 := by
  have hd : ∀ i, δ i * x i = 0 := by
    intro i
    by_cases hi : δ i = 0
    · simp [hi]
    · rw [(kernel_restrictions (fun _ => ρ) δ E hs hn hδ hrow hx).1 i
        (lt_of_le_of_ne (hδ i) (Ne.symm hi)), mul_zero]
  have hcol (j : ι) : (∑ i, E i j) = ρ - δ j := by
    calc
      (∑ i, E i j) = ∑ i, E j i := sum_congr rfl fun i _ => hs i j
      _ = ρ - δ j := by linarith [hrow j]
  have he : (∑ i, ∑ j, E i j * x j) = ρ * ∑ j, x j := by
    rw [sum_comm]
    simp_rw [← sum_mul, hcol]
    calc
      (∑ j, (ρ - δ j) * x j) = ∑ j, ρ * x j := by
        apply sum_congr rfl
        intro j _
        nlinarith [hd j]
      _ = ρ * ∑ j, x j := (mul_sum _ _ _).symm
  have hsum : (∑ i, ((Matrix.diagonal (fun _ => ρ) + E) *ᵥ x) i) = 0 := by
    rw [hx]
    simp
  rw [Matrix.add_mulVec] at hsum
  simp only [Pi.add_apply, Matrix.mulVec_diagonal] at hsum
  simp only [Matrix.mulVec, dotProduct, sum_add_distrib] at hsum
  rw [← mul_sum, he] at hsum
  have hp : ρ * (∑ i, x i) = 0 := by linarith
  exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt hρ)

omit [DecidableEq ι] in
private theorem constant_posSemidef (lam : ℝ) (hlam : 0 ≤ lam) :
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

/-- Nonnegative constant Gram terms preserve the signless kernel. -/
theorem ker_add_constant_eq (ρ lam : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hδ : ∀ i, 0 ≤ δ i)
    (hrow : ∀ i, (∑ j, E i j) + δ i = ρ) :
    LinearMap.ker
      (Matrix.diagonal (fun _ => ρ) + E + Matrix.of (fun _ _ => lam)).mulVecLin =
      LinearMap.ker (Matrix.diagonal (fun _ => ρ) + E).mulVecLin := by
  apply le_antisymm
  · exact ker_add_le_of_posSemidef
      (signless_posSemidef (fun _ => ρ) δ E hs hn hδ hrow)
      (constant_posSemidef lam hlam)
  · intro x hx
    change (Matrix.diagonal (fun _ => ρ) + E) *ᵥ x = 0 at hx
    change (Matrix.diagonal (fun _ => ρ) + E + Matrix.of (fun _ _ => lam)) *ᵥ x = 0
    have hxsum := kernel_sum_zero ρ E δ hρ hs hn hδ hrow hx
    rw [Matrix.add_mulVec, hx, zero_add]
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← mul_sum, hxsum, mul_zero]

/-- Twice the actual Gram rank pays for every row and every positive deficit.
The remainder may be any positive-semidefinite matrix. -/
theorem gram_rank_budget
    (R : Matrix ι κ ℝ) (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ)
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    (hgram : R * R.transpose = Matrix.diagonal (fun _ => ρ) + E + P) :
    Fintype.card ι + (univ.filter fun i => 0 < δ i).card ≤ 2 * R.rank := by
  classical
  have hnull := two_mul_nullity_le_zero_count ρ E δ hρ hs hn hz hδ hrow
  have hker := ker_add_le_of_posSemidef
    (signless_posSemidef (fun _ => ρ) δ E hs hn hδ hrow) hP
  rw [← hgram] at hker
  have hdim := Submodule.finrank_mono hker
  have htotal : R.rank +
      finrank ℝ (LinearMap.ker (R * R.transpose).mulVecLin) = Fintype.card ι := by
    have ht : (R * R.transpose).rank +
        finrank ℝ (LinearMap.ker (R * R.transpose).mulVecLin) = Fintype.card ι := by
      simpa [Matrix.rank] using
        LinearMap.finrank_range_add_finrank_ker (R * R.transpose).mulVecLin
    simpa only [Matrix.rank_self_mul_transpose] using ht
  have hpartition : (univ.filter fun i => δ i = 0).card +
      (univ.filter fun i => 0 < δ i).card = Fintype.card ι := by
    have hpositive : (univ.filter fun i => 0 < δ i) =
        univ.filter (fun i => ¬ δ i = 0) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      exact lt_iff_le_and_ne.trans (by simp [hδ i, ne_comm])
    rw [hpositive, card_filter_add_card_filter_not, card_univ]
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- Centered constant-row-sum matrices annihilate the all-ones vector. -/
theorem centered_mulVec_one (R : Matrix ι κ ℝ) (r : ℝ)
    (hb : 0 < Fintype.card κ) (hrow : ∀ i, ∑ j, R i j = r) :
    centered R r *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have hbR : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  ext i
  simp only [centered, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.of_apply,
    mul_one, Pi.zero_apply, sum_sub_distrib, hrow, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The row Gram matrix after subtracting the common row average. -/
theorem centered_gram (R : Matrix ι κ ℝ) (r : ℝ)
    (hb : 0 < Fintype.card κ) (hrow : ∀ i, ∑ j, R i j = r) :
    centered R r * (centered R r).transpose = R * R.transpose -
      Matrix.of (fun _ _ => r^2 / (Fintype.card κ : ℝ)) := by
  have hbR : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  ext i j
  simp only [centered, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.of_apply]
  have he : (∑ k, (R i k - r / (Fintype.card κ : ℝ)) *
      (R j k - r / (Fintype.card κ : ℝ))) =
      (∑ k, R i k * R j k) - (r / (Fintype.card κ : ℝ)) * (∑ k, R i k) -
        (r / (Fintype.card κ : ℝ)) * (∑ k, R j k) +
          (Fintype.card κ : ℝ) * (r / (Fintype.card κ : ℝ))^2 := by
    simp_rw [show ∀ k, (R i k - r / (Fintype.card κ : ℝ)) *
      (R j k - r / (Fintype.card κ : ℝ)) = R i k * R j k -
        (r / (Fintype.card κ : ℝ)) * R i k -
        (r / (Fintype.card κ : ℝ)) * R j k +
          (r / (Fintype.card κ : ℝ))^2 by intro k; ring]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
      nsmul_eq_mul]
  rw [he, hrow, hrow]
  field_simp
  ring

/-- Centering preserves rank when the centered constant Gram term remains
nonnegative. No nonempty-row assumption or component classification is needed. -/
theorem centered_rank_eq
    (R : Matrix ι κ ℝ) (r ρ lam : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hb : 0 < Fintype.card κ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hδ : ∀ i, 0 ≤ δ i) (hbalance : ∀ i, (∑ j, E i j) + δ i = ρ)
    (hrow : ∀ i, ∑ j, R i j = r)
    (hgram : R * R.transpose =
      Matrix.diagonal (fun _ => ρ) + E + Matrix.of (fun _ _ => lam))
    (hcenter : r^2 ≤ (Fintype.card κ : ℝ) * lam) :
    (centered R r).rank = R.rank := by
  have hbR : (0 : ℝ) < Fintype.card κ := by exact_mod_cast hb
  have hconstant : 0 ≤ lam - r^2 / (Fintype.card κ : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hbR).mpr (by simpa only [mul_comm] using hcenter)
  have hgramC : centered R r * (centered R r).transpose =
      Matrix.diagonal (fun _ => ρ) + E +
        Matrix.of (fun _ _ => lam - r^2 / (Fintype.card κ : ℝ)) := by
    rw [centered_gram R r hb hrow, hgram]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply]
    ring
  have hker : LinearMap.ker (centered R r * (centered R r).transpose).mulVecLin =
      LinearMap.ker (R * R.transpose).mulVecLin := by
    rw [hgramC, hgram, ker_add_constant_eq ρ _ E δ hρ hconstant hs hn hδ hbalance,
      ker_add_constant_eq ρ lam E δ hρ hlam hs hn hδ hbalance]
  have hR : R.rank + finrank ℝ (LinearMap.ker (R * R.transpose).mulVecLin) =
      Fintype.card ι := by
    have ht := LinearMap.finrank_range_add_finrank_ker (R * R.transpose).mulVecLin
    change (R * R.transpose).rank + _ = _ at ht
    simpa only [Matrix.rank_self_mul_transpose, Module.finrank_pi,
      Module.finrank_self, sum_const, card_univ, smul_eq_mul, mul_one] using ht
  have hC : (centered R r).rank +
      finrank ℝ (LinearMap.ker (centered R r * (centered R r).transpose).mulVecLin) =
      Fintype.card ι := by
    have ht := LinearMap.finrank_range_add_finrank_ker
      (centered R r * (centered R r).transpose).mulVecLin
    change (centered R r * (centered R r).transpose).rank + _ = _ at ht
    simpa only [Matrix.rank_self_mul_transpose, Module.finrank_pi,
      Module.finrank_self, sum_const, card_univ, smul_eq_mul, mul_one] using ht
  rw [hker] at hC
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- A nonempty all-ones kernel vector forces at least one unused column rank. -/
theorem one_le_corank_of_mulVec_one_eq_zero (T : Matrix ι κ ℝ)
    (hb : 0 < Fintype.card κ) (hzero : T *ᵥ (fun _ => (1 : ℝ)) = 0) :
    1 ≤ Fintype.card κ - T.rank := by
  have hone : (fun _ : κ => (1 : ℝ)) ≠ 0 := by
    intro h
    obtain ⟨j⟩ := Fintype.card_pos_iff.mp hb
    have hj := congr_fun h j
    norm_num at hj
  have hnull : 0 < finrank ℝ (LinearMap.ker T.mulVecLin) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨fun _ => (1 : ℝ), hzero⟩, ?_⟩
    intro h
    exact hone (congr_arg Subtype.val h)
  have htotal : T.rank + finrank ℝ (LinearMap.ker T.mulVecLin) = Fintype.card κ := by
    simpa [Matrix.rank] using LinearMap.finrank_range_add_finrank_ker T.mulVecLin
  omega

/-- The centering and positive-deficit budget used in support completion.
All hypotheses concern the supplied real matrix and its exact Gram identity;
no binary-entry premise or nonempty-row premise is imposed. -/
theorem centered_completion
    (R : Matrix ι κ ℝ) (r ρ lam : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hb : 0 < Fintype.card κ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hz : ∀ i, E i i = 0) (hδ : ∀ i, 0 ≤ δ i)
    (hbalance : ∀ i, (∑ j, E i j) + δ i = ρ)
    (hrow : ∀ i, ∑ j, R i j = r)
    (hgram : R * R.transpose =
      Matrix.diagonal (fun _ => ρ) + E + Matrix.of (fun _ _ => lam))
    (hcenter : r^2 ≤ (Fintype.card κ : ℝ) * lam) :
    (centered R r).rank = R.rank ∧
      centered R r *ᵥ (fun _ => (1 : ℝ)) = 0 ∧
      1 ≤ Fintype.card κ - R.rank ∧
      Fintype.card ι + (univ.filter fun i => 0 < δ i).card ≤ 2 * R.rank := by
  classical
  have hrank := centered_rank_eq R r ρ lam E δ hρ hlam hb hs hn hδ hbalance
    hrow hgram hcenter
  have hzero := centered_mulVec_one R r hb hrow
  refine ⟨hrank, hzero, ?_, ?_⟩
  · rw [← hrank]
    exact one_le_corank_of_mulVec_one_eq_zero (centered R r) hb hzero
  · exact gram_rank_budget R ρ E δ hρ hs hn hz hδ hbalance
      (Matrix.of (fun _ _ => lam)) (constant_posSemidef lam hlam) hgram

end CoveringDesigns.BoundaryRank
