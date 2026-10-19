import CoveringDesigns.TwoKMinusC.Algebra

/-! The sharper offset-three scalar comparison is independent of geometry. -/
namespace CoveringDesigns.TwoKMinusCGeneral
open TwoKMinusC

theorem Q_three (k : ℕ) : Q 3 k =
    14*(k : ℝ)*(2*k-3)/(2*k^2+5*k+42) := by
  unfold Q numerator denominator offsetDefect
  norm_num
  ring

theorem thirteen_lt_Q_three {k : ℕ} (hk : 59≤k) : 13<Q 3 k := by
  rw [Q_three]
  have hkR : (59 : ℝ)≤k := by exact_mod_cast hk
  have hd : (0 : ℝ)<2*(k : ℝ)^2+5*k+42 := by positivity
  apply (lt_div_iff₀ hd).mpr
  nlinarith [sq_nonneg ((k : ℝ)-59)]

end CoveringDesigns.TwoKMinusCGeneral
