import CoveringDesigns.TwoKMinusC.Algebra

/-! Infinite-range strict comparisons; no parameter enumeration.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusC

theorem Q_two (k : ℕ) :
    Q 2 k = 2*((k : ℝ)-1)*(7*(k : ℝ)-3)/((k : ℝ)^2+k+6) := by
  have hD : (k : ℝ)^2+k+6 ≠ 0 := by positivity
  have hD2 := ne_of_gt (denominator_pos (k := k) (by norm_num : 2≤2))
  unfold Q numerator denominator offsetDefect at *
  norm_num
  field_simp
  ring

theorem twelve_lt_Q_two {k : ℕ} (hk : 18≤k) : 12 < Q 2 k := by
  have hkR : (18 : ℝ)≤k := by exact_mod_cast hk
  rw [Q_two, lt_div_iff₀ (by positivity : (0 : ℝ)<(k : ℝ)^2+k+6)]
  nlinarith [sq_nonneg ((k : ℝ)-18)]

theorem thirteen_lt_Q_two {k : ℕ} (hk : 36≤k) : 13 < Q 2 k := by
  have hkR : (36 : ℝ)≤k := by exact_mod_cast hk
  rw [Q_two, lt_div_iff₀ (by positivity : (0 : ℝ)<(k : ℝ)^2+k+6)]
  nlinarith [sq_nonneg ((k : ℝ)-36)]

end CoveringDesigns.TwoKMinusC
