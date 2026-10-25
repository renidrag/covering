import CoveringDesigns.SevenBlock.Fano
import Mathlib.Tactic.Linarith

/-! The eight binary characters used after actual affine recognition.
Only the fixed character table is checked by reduction. The coefficient
identities are polynomial proofs for arbitrary signed integer weights. -/
namespace CoveringDesigns.C19_9_3
open Finset

/-- Nonconstant characters on binary points 0,…,7, in directions 1,…,7. -/
def character : Fin 7 → Fin 8 → ℤ :=
  ![![1,-1,1,-1,1,-1,1,-1], ![1,1,-1,-1,1,1,-1,-1],
    ![1,-1,-1,1,1,-1,-1,1], ![1,1,1,1,-1,-1,-1,-1],
    ![1,-1,1,-1,-1,1,-1,1], ![1,1,-1,-1,-1,-1,1,1],
    ![1,-1,-1,1,-1,1,1,-1]]

section Table
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem character_sign : ∀ n x, character n x = 1 ∨ character n x = -1 := by
  decide +kernel

theorem character_balanced : ∀ n, ∑ x, character n x = 0 := by decide +kernel

theorem character_orthogonal : ∀ n m,
    ∑ x, character n x * character m x = if n = m then 8 else 0 := by decide +kernel

end Table

theorem coefficient_extraction (c : Fin 7 → ℤ) (n : Fin 7) :
    (∑ x : Fin 8, (∑ m : Fin 7, c m * character m x) * character n x) = 8 * c n := by
  simp_rw [sum_mul,mul_assoc]
  rw [sum_comm]
  simp_rw [← mul_sum,character_orthogonal]
  simp [mul_ite,mul_comm]

theorem character_parseval (c : Fin 7 → ℤ) :
    (∑ x : Fin 8, (∑ n : Fin 7, c n * character n x)^2) = 8 * ∑ n, (c n)^2 := by
  calc
    _ = ∑ x : Fin 8, ∑ n : Fin 7, c n * ((∑ m : Fin 7, c m * character m x) * character n x) := by
      apply sum_congr rfl
      intro x _
      rw [pow_two,mul_sum]
      apply sum_congr rfl
      intro n _
      ring
    _ = ∑ n : Fin 7, c n * (∑ x : Fin 8, (∑ m : Fin 7, c m * character m x) * character n x) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = 8 * ∑ n : Fin 7, (c n)^2 := by
      simp_rw [coefficient_extraction]
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring

theorem coefficients_zero (c : Fin 7 → ℤ)
    (h : ∀ x, (∑ n : Fin 7, c n * character n x) = 0) : ∀ n, c n = 0 := by
  intro n
  have hh := coefficient_extraction c n
  simp only [h,zero_mul,sum_const_zero] at hh
  omega

/-- An integral combination taking only the values ±1 is one signed
character. The proof uses Parseval and a nonnegative integer budget. -/
theorem character_unit_square (c : Fin 7 → ℤ)
    (h : ∀ x, (∑ n : Fin 7, c n * character n x)^2 = 1) :
    ∃ n, (c n = 1 ∨ c n = -1) ∧ ∀ m, m ≠ n → c m = 0 := by
  have hs : ∑ n, (c n)^2 = 1 := by
    have hh := character_parseval c
    simp only [h,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    omega
  have hex : ∃ n, c n ≠ 0 := by
    by_contra hn
    push Not at hn
    simp only [hn,zero_pow (by decide : 2 ≠ 0),sum_const_zero] at hs
    contradiction
  obtain ⟨n,hn⟩ := hex
  have hnle : (c n)^2 ≤ 1 := by
    rw [← hs]
    exact single_le_sum (fun m _ => sq_nonneg (c m)) (mem_univ n)
  have hnge : 1 ≤ (c n)^2 := by
    have hsplit : c n ≤ -1 ∨ 1 ≤ c n := by omega
    rcases hsplit with hsplit | hsplit <;> nlinarith
  have hne : c n = 1 ∨ c n = -1 := by
    have hlo : -1 ≤ c n := by nlinarith
    have hhi : c n ≤ 1 := by nlinarith
    omega
  refine ⟨n,hne,?_⟩
  intro m hmn
  have he : (∑ k ∈ (univ : Finset (Fin 7)).erase n, (c k)^2) + (c n)^2 = 1 := by
    rw [sum_erase_add _ _ (mem_univ n),hs]
  have hml : (c m)^2 ≤ ∑ k ∈ (univ : Finset (Fin 7)).erase n, (c k)^2 :=
    single_le_sum (fun k _ => sq_nonneg (c k)) (mem_erase.mpr ⟨hmn,mem_univ _⟩)
  nlinarith [sq_nonneg (c m)]

#guard_standard_axioms character_sign character_balanced character_orthogonal
  coefficient_extraction character_parseval coefficients_zero character_unit_square

end CoveringDesigns.C19_9_3
