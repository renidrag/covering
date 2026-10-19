import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The Caro–Tuza function and the scalar estimates used in Horsley's
maximum-degree deletion proof (Lemma 7, properties F1/F2).
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.CaroTuza

/-- The Caro–Tuza potential contribution; only nonnegative inputs are used. -/
noncomputable def f (m : ℕ) (x : ℝ) : ℝ :=
  if x ≤ m then 1-x/(2*m) else (m+1)/(2*(x+1))

theorem f_low {m : ℕ} {x : ℝ} (hx : x ≤ m) : f m x = 1-x/(2*m) :=
  if_pos hx

theorem f_high {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : (m : ℝ) ≤ x) :
    f m x = (m+1)/(2*(x+1)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases h : x ≤ m
  · have he : x = m := le_antisymm h hx
    subst x
    rw [f_low le_rfl]
    field_simp
    <;> ring
  · exact if_neg h

theorem f_zero (m : ℕ) : f m 0 = 1 := by simp [f]

theorem f_join {m : ℕ} (hm : 0 < m) : f m m = 1/2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [f_low le_rfl]
  field_simp
  <;> ring

theorem f_nonneg {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f m x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases h : x ≤ m
  · rw [f_low h]
    have : x/(2*m) ≤ (1 : ℝ) := (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith
  · rw [f_high hm (le_of_not_ge h)]
    positivity

theorem f_le_one {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) : f m x ≤ 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases h : x ≤ m
  · rw [f_low h]
    have : 0 ≤ x/(2*(m : ℝ)) := by positivity
    linarith
  · rw [f_high hm (le_of_not_ge h)]
    apply (div_le_iff₀ (by positivity)).mpr
    have := le_of_not_ge h
    linarith

/-- Monotonicity on the domain of weighted degrees, including the join. -/
theorem f_antitone {m : ℕ} (hm : 0 < m) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : f m y ≤ f m x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hy : y ≤ m
  · rw [f_low hy, f_low (hxy.trans hy)]
    exact sub_le_sub_left (div_le_div_of_nonneg_right hxy (by positivity)) 1
  · rw [f_high hm (le_of_not_ge hy)]
    by_cases hxm : x ≤ m
    · rw [f_low hxm]
      have h₁ : ((m : ℝ)+1)/(2*(y+1)) ≤ 1/2 := by
        apply (div_le_iff₀ (by linarith)).mpr
        linarith
      have h₂ : x/(2*(m : ℝ)) ≤ 1/2 := by
        apply (div_le_iff₀ (by positivity)).mpr
        linarith
      linarith
    · rw [f_high hm (le_of_not_ge hxm)]
      exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- Horsley's F2. The crossing-join case is a sum of nonnegative products. -/
theorem decrement {m : ℕ} (hm : 0 < m) {x y : ℝ}
    (hx : (m : ℝ) ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x) :
    y*((m : ℝ)+1)/(2*x*(x+1)) ≤ f m (x-y)-f m x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hxp : 0 < x := hm'.trans_le hx
  rw [f_high hm hx]
  by_cases hl : x-y ≤ m
  · rw [f_low hl]
    have hd : 0 < 2*(m : ℝ)*x*(x+1) := by positivity
    have he : 1-(x-y)/(2*(m : ℝ))-((m : ℝ)+1)/(2*(x+1)) -
        y*((m : ℝ)+1)/(2*x*(x+1)) =
        ((x+1)*(x-m)*(m+y-x)+(m : ℝ)*(y-1)*(x-m))/(2*m*x*(x+1)) := by
      field_simp
      <;> ring
    have hn : 0 ≤ (x+1)*(x-m)*(m+y-x)+(m : ℝ)*(y-1)*(x-m) := by
      apply add_nonneg
      · exact mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hx)) (by linarith)
      · exact mul_nonneg (mul_nonneg hm'.le (by linarith)) (sub_nonneg.mpr hx)
    have := div_nonneg hn hd.le
    linarith [he]
  · have hh : (m : ℝ) ≤ x-y := le_of_not_ge hl
    have hxy1 : x-y+1 ≠ 0 := ne_of_gt (by linarith)
    rw [f_high hm hh]
    have he : ((m : ℝ)+1)/(2*(x-y+1))-((m : ℝ)+1)/(2*(x+1)) =
        y*((m : ℝ)+1)/(2*(x+1)*(x-y+1)) := by
      field_simp [hxy1]
      <;> ring
    rw [he]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have ht : 0 ≤ 2*(x+1)*(y-1) := by positivity
    nlinarith only [ht]

/-- Uniform gain estimate when X is bounded by the degree D of the deleted
vertex. Low-degree vertices may carry arbitrarily small positive weights. -/
theorem decrement_of_le_max {m : ℕ} (hm : 0 < m) {D X y : ℝ}
    (hD : (m : ℝ) ≤ D) (hX : 0 ≤ X) (hXD : X ≤ D)
    (hy : 0 ≤ y) (hyX : y ≤ X)
    (hunit : (m : ℝ) ≤ X → 0 < y → 1 ≤ y) :
    y * (((m : ℝ)+1)/(2*D*(D+1))) ≤ f m (X-y)-f m X := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hDp : 0 < D := hm'.trans_le hD
  by_cases hz : y = 0
  · simp [hz]
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hz)
  by_cases hXm : X < m
  · rw [f_low (by linarith : X-y ≤ m), f_low hXm.le]
    have hden : (m : ℝ)*((m : ℝ)+1) ≤ D*(D+1) :=
      mul_le_mul hD (by linarith) (by positivity) hDp.le
    have hc : ((m : ℝ)+1)/(2*D*(D+1)) ≤ 1/(2*m) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hden]
    have hg := mul_le_mul_of_nonneg_left hc hy
    convert hg using 1 <;> ring
  · have hXm' := le_of_not_gt hXm
    have hXp : 0 < X := hm'.trans_le hXm'
    have hc : y*((m : ℝ)+1)/(2*D*(D+1)) ≤
        y*((m : ℝ)+1)/(2*X*(X+1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have := mul_le_mul hXD (by linarith : X+1 ≤ D+1) (by positivity) hDp.le
      nlinarith only [this]
    calc
      y * (((m : ℝ)+1)/(2*D*(D+1))) = y*((m : ℝ)+1)/(2*D*(D+1)) := by ring
      _ ≤ y*((m : ℝ)+1)/(2*X*(X+1)) := hc
      _ ≤ _ := decrement hm hXm' (hunit hXm' hyp) hyX

end CoveringDesigns.CaroTuza
