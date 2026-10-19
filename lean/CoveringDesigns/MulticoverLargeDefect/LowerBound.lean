import CoveringDesigns.MulticoverLargeDefect.Selection
import CoveringDesigns.MulticoverLargeDefect.Counting
import CoveringDesigns.MulticoverIncidence.LowerBound

/-! Horsley–Singh Theorem 15 for indexed coverings of arbitrary positive multiplicity and arbitrary admissible s.
The two counting branches cover the source's full defect range.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.MulticoverLargeDefect
open Finset HigherIncidence MulticoverIncidence LargeDefect
universe u w
variable {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι]

noncomputable def value (v k s : ℕ) (b : ℕ → ℕ) : ℝ :=
  ratio (v.choose s) (k.choose s) (b s)
    (alpha (coefficient s b s) (defect v k s b))
    (beta (k.choose s) (coefficient s b s) (defect v k s b))

noncomputable def bound (v k s : ℕ) (b : ℕ → ℕ) : ℕ := ⌈value v k s b⌉₊

theorem bound_denominator_pos {v k s : ℕ} {b : ℕ → ℕ}
    (hK : 0 < k.choose s) (ha : 0 ≤ coefficient s b s) (hd : 0 ≤ defect v k s b) :
    0 < (k.choose s : ℝ) *
      (alpha (coefficient s b s) (defect v k s b) -
        beta (k.choose s) (coefficient s b s) (defect v k s b)) + 1 := by
  apply ratio_denominator_pos
  exact beta_le_alpha hK (by exact_mod_cast ha) (by exact_mod_cast hd)

/-- Exact equivalence with the division-free form of the displayed bound. -/
theorem bound_le_iff {v k s n : ℕ} {b : ℕ → ℕ}
    (hK : 0 < k.choose s) (ha : 0 ≤ coefficient s b s) (hd : 0 ≤ defect v k s b) :
    bound v k s b ≤ n ↔
      (v.choose s : ℝ) * ((b s : ℝ) *
        (alpha (coefficient s b s) (defect v k s b) -
          beta (k.choose s) (coefficient s b s) (defect v k s b)) +
        alpha (coefficient s b s) (defect v k s b)) ≤
      (n : ℝ) * ((k.choose s : ℝ) *
        (alpha (coefficient s b s) (defect v k s b) -
          beta (k.choose s) (coefficient s b s) (defect v k s b)) + 1) := by
  exact ceiling_le_iff (beta_le_alpha hK (by exact_mod_cast ha) (by exact_mod_cast hd))

/-- Nonnegativity identifies the natural ceiling with the usual nonnegative bound. -/
theorem value_nonneg {v k s : ℕ} {b : ℕ → ℕ}
    (hK : 0 < k.choose s) (ha : 0 ≤ coefficient s b s) (hd : 0 ≤ defect v k s b) :
    0 ≤ value v k s b := by
  have haR : (0 : ℝ) ≤ coefficient s b s := by exact_mod_cast ha
  have hdR : (0 : ℝ) ≤ defect v k s b := by exact_mod_cast hd
  have hAB := beta_le_alpha hK haR hdR
  have hA := alpha_pos haR hdR
  have hD := bound_denominator_pos hK ha hd
  unfold value ratio
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hD.le

/-- The structural theorem before the universal smaller-cover bridge.
The diagonal bound a<m is explicit here and is derived from Parameters below. -/
theorem lower_bound_of_multiplicities {B : ι → Finset α} {k s : ℕ} {b : ℕ → ℕ}
    (hu : Multicover.Uniform B k)
    (hc : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (hmK : b s < k.choose s) (ham : coefficient s b s < b s)
    (ha : 1 ≤ coefficient s b s)
    (had : coefficient s b s ≤ defect (Fintype.card α) k s b) :
    bound (Fintype.card α) k s b ≤ Fintype.card ι := by
  have hK : 0 < k.choose s := by omega
  have ha0 : 0 ≤ coefficient s b s := by omega
  have hd0 : 0 ≤ defect (Fintype.card α) k s b := by omega
  have haR : (0 : ℝ) ≤ coefficient s b s := by exact_mod_cast ha0
  have hdR : (0 : ℝ) ≤ defect (Fintype.card α) k s b := by exact_mod_cast hd0
  have hAB := beta_le_alpha hK haR hdR
  have hb0 (X : Finset α) (hx : X.card=s) : b s ≤ indexedSubsetDegree B X := by
    simpa [hx] using hb X (by omega) (by omega)
  by_cases hsplit : defect (Fintype.card α) k s b+2 ≤ (k.choose s : ℤ)
  · have hc2 : 2*beta (k.choose s) (coefficient s b s) (defect (Fintype.card α) k s b) ≤
        alpha (coefficient s b s) (defect (Fintype.card α) k s b) :=
      (coefficient_two_level_iff hK haR hdR).mpr (by exact_mod_cast hsplit)
    exact two_level_ceiling hu (beta_pos hK haR hdR).le hc2 hb0
      (selection_bound hu hK hc hb ha had)
  · have hKd : (k.choose s : ℤ) ≤ defect (Fintype.card α) k s b+1 := by omega
    have hf := fallback_coefficient ha0 hd0 hKd ham
    apply Nat.ceil_le.mpr
    apply (ratio_le_incidence ((Fintype.card α).choose s) (k.choose s) (b s) hK hAB
      (by nlinarith only [hf.1, hf.2])).trans
    apply (div_le_iff₀ (by exact_mod_cast hK : (0 : ℝ) < k.choose s)).mpr
    have hi : ((Fintype.card α).choose s : ℝ)*b s ≤ (k.choose s : ℝ)*Fintype.card ι := by
      exact_mod_cast incidence_bound hu hb0
    simpa only [mul_comm] using hi

/-- Theorem 15 for every positive λ and every admissible s, with the source's complete
parameter and universal smaller-cover hypotheses. No rank or selection
assumption, or restriction to the two-level counting range, is added. -/
theorem lower_bound {B : ι → Finset α} {lam v k t s : ℕ} {b : ℕ → ℕ}
    (hp : MulticoverIncidence.Parameters lam v k t s b)
    (hb : MulticoverIncidence.SmallerBounds.{u,w} lam v k t s b)
    (hn : Fintype.card α=v) (h : Multicover.IsCover B k t lam)
    (hmK : b s < k.choose s) (ha : 1 ≤ coefficient s b s)
    (had : coefficient s b s ≤ defect v k s b) : bound v k s b ≤ Fintype.card ι := by
  rw [← hn] at had ⊢
  exact lower_bound_of_multiplicities h.1 (fun j hj => hp.coefficients j hj.le)
    (multiplicity_bounds hp.strength hb hn h) hmK hp.diagonal_lt ha had

/-- Division-free Theorem 15, with the same complete covering hypotheses. -/
theorem lower_bound_inequality {B : ι → Finset α} {lam v k t s : ℕ} {b : ℕ → ℕ}
    (hp : MulticoverIncidence.Parameters lam v k t s b)
    (hb : MulticoverIncidence.SmallerBounds.{u,w} lam v k t s b)
    (hn : Fintype.card α=v) (h : Multicover.IsCover B k t lam)
    (hmK : b s < k.choose s) (ha : 1 ≤ coefficient s b s)
    (had : coefficient s b s ≤ defect v k s b) :
    (v.choose s : ℝ) * ((b s : ℝ) *
      (alpha (coefficient s b s) (defect v k s b) -
        beta (k.choose s) (coefficient s b s) (defect v k s b)) +
      alpha (coefficient s b s) (defect v k s b)) ≤
    (Fintype.card ι : ℝ) * ((k.choose s : ℝ) *
      (alpha (coefficient s b s) (defect v k s b) -
        beta (k.choose s) (coefficient s b s) (defect v k s b)) + 1) :=
  (bound_le_iff (by omega) (by omega) (by omega)).mp
    (lower_bound hp hb hn h hmK ha had)

end CoveringDesigns.MulticoverLargeDefect
