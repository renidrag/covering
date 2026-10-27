import CoveringDesigns.Qk_K_2.Exclusions
import Mathlib.Data.Rat.Lemmas

/-! Square-parity consumers of the unchanged twisted determinant. -/
namespace CoveringDesigns.PairConsequences
open PairEquality

def determinantValue (q : ℕ) : ℤ :=
  ((q-1 : ℕ) : ℤ)^(q*(q+1)/2) * (q+1 : ℕ)^(q*(q+1)/2+1)

/-- Cancelling a nonzero integer square preserves integral squareness. -/
theorem square_factor_iff (c z : ℤ) (hc : c ≠ 0) :
    IsSquare (c^2*z) ↔ IsSquare z := by
  rw [← Rat.isSquare_intCast_iff, ← Rat.isSquare_intCast_iff]
  push_cast
  constructor
  · rintro ⟨d,hd⟩
    refine ⟨d / c, ?_⟩
    have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    field_simp
    nlinarith [hd]
  · rintro ⟨d,hd⟩
    exact ⟨c*d, by rw [hd]; ring⟩

/-- Equivalent square-parity criterion, expressed directly in the half-order
exponent. Positivity is explicit; q=0,1 are deliberately outside its scope. -/
theorem determinant_square_parity {q : ℕ} (hq : 2 ≤ q) :
    IsSquare (determinantValue q) ↔
      if Even (q*(q+1)/2) then IsSquare (q+1 : ℤ) else IsSquare ((q-1 : ℕ) : ℤ) := by
  let a := q*(q+1)/2
  have hm : (0 : ℤ) < (q-1 : ℕ) := by exact_mod_cast (show 0 < q-1 by omega)
  have hp : (0 : ℤ) < (q+1 : ℕ) := by positivity
  by_cases he : Even a
  · obtain ⟨h,hh⟩ := he
    have hf : determinantValue q =
        (((q-1 : ℕ) : ℤ)^h * (q+1 : ℕ)^h)^2 * (q+1 : ℤ) := by
      unfold determinantValue
      change ((q-1 : ℕ) : ℤ)^a * (q+1 : ℕ)^(a+1) = _
      rw [hh]
      push_cast
      simp only [pow_add, pow_one]
      ring
    rw [if_pos (show Even (q*(q+1)/2) from ⟨h,hh⟩),hf]
    exact square_factor_iff _ _ (ne_of_gt (mul_pos (pow_pos hm _) (pow_pos hp _)))
  · have ha : a % 2 = 1 := by rw [Nat.even_iff] at he; omega
    let h := a/2
    have hh : a = h+h+1 := by omega
    have hf : determinantValue q =
        (((q-1 : ℕ) : ℤ)^h * (q+1 : ℕ)^(h+1))^2 * ((q-1 : ℕ) : ℤ) := by
      unfold determinantValue
      change ((q-1 : ℕ) : ℤ)^a * (q+1 : ℕ)^(a+1) = _
      rw [hh]
      simp only [pow_add, pow_one]
      ring
    rw [if_neg he,hf]
    exact square_factor_iff _ _ (ne_of_gt (mul_pos (pow_pos hm _) (pow_pos hp _)))

theorem nonsquare_six (d : ℤ) : d^2 ≠ (5 : ℤ)^21 * 7^22 := by
  intro hd
  have hs : IsSquare (determinantValue 6) := ⟨d, by simpa [determinantValue,pow_two] using hd.symm⟩
  have hfive := (determinant_square_parity (q := 6) (by decide)).mp hs
  norm_num [Even] at hfive
  obtain ⟨z,hz⟩ := hfive
  by_cases h : z ≤ 2
  · nlinarith
  · have : 3 ≤ z := by omega
    nlinarith

theorem no_twisted_six {I : Type*} [Fintype I] [DecidableEq I]
    {H : Finset (Finset I)} (T : IsTwistedPlane 6 H) : False :=
  Qk_K_2.exclude_twisted (by decide) nonsquare_six T

theorem indexed_six {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {k : ℕ} {B : I → Finset X}
    (hk : 6 ≤ k) (hv : Fintype.card X = 6*k)
    (hB : Multicover.IsCover B k 2 1) (hnd : ¬ 6 ∣ k) :
    43 ≤ Fintype.card I :=
  Qk_K_2.indexed_exclusion (by decide) hk hv hB hnd no_twisted_six

theorem lower_bound_six {X : Type*} [Fintype X] {C : Family X} {k : ℕ}
    (hk : 6 ≤ k) (hv : Fintype.card X = 6*k) (hC : IsCover C k 2)
    (hnd : ¬ 6 ∣ k) : 43 ≤ C.card := by
  classical
  simpa using indexed_six hk hv ((Multicover.ofFamily_isCover_one C k 2).mpr hC) hnd

end CoveringDesigns.PairConsequences
