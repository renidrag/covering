import CoveringDesigns.TwistedArithmetic.MatePairs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Determinant of the mate-pair Gram matrix, by pair sums and differences. -/
namespace CoveringDesigns.TwistedArithmetic
open Matrix
variable {R : Type*} [Fintype R] [DecidableEq R]

private def ones : Matrix R R ℚ := fun _ _ => 1

def pairedGram (a : ℚ) : Matrix (R ⊕ R) (R ⊕ R) ℚ :=
  fromBlocks (a • 1 + ones) (1 + ones) (1 + ones) (a • 1 + ones)

theorem pairedGram_apply (a : ℚ) (x y : R ⊕ R) : pairedGram a x y =
    (if x = y then a else 0) + 1 + (if y = x.swap then 1 else 0) := by
  rcases x with i|i <;> rcases y with j|j <;>
    simp [pairedGram,ones,Matrix.fromBlocks,Matrix.one_apply,Matrix.add_apply,
      Matrix.smul_apply,smul_eq_mul,eq_comm] <;> split_ifs <;> ring

private theorem scalar_ones_det (a : ℚ) (ha : a ≠ 0) :
    (a • (1 : Matrix R R ℚ) + (2 : ℚ) • ones).det =
      a ^ Fintype.card R * (1 + 2 * Fintype.card R / a) := by
  have he : a • (1 : Matrix R R ℚ) + (2 : ℚ) • ones =
      a • (1 + replicateCol Unit (fun _ : R => 2/a) * replicateRow Unit (fun _ : R => (1 : ℚ))) := by
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,
      Matrix.replicateCol_apply,Matrix.replicateRow_apply,Fintype.sum_unique,mul_one]
    change a * (1 : Matrix R R ℚ) i j + 2 * 1 = a * ((1 : Matrix R R ℚ) i j + 2/a)
    field_simp
  rw [he,det_smul,det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct,one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

/-- Reusable determinant for a paired mate matrix; no plane existence is assumed. -/
theorem pairedGram_det (a : ℚ) (ha : a+1 ≠ 0) :
    (pairedGram (R := R) a).det = (a-1)^Fintype.card R *
      (a+1)^Fintype.card R * (1 + 2 * Fintype.card R / (a+1)) := by
  let S : Matrix (R ⊕ R) (R ⊕ R) ℚ := fromBlocks 1 1 1 (-1)
  let D : Matrix (R ⊕ R) (R ⊕ R) ℚ :=
    fromBlocks ((a+1) • 1 + (2 : ℚ) • ones) 0 0 ((a-1) • 1)
  have hs : S.det ≠ 0 := by
    have he : (-1 : Matrix R R ℚ) - 1 = (-2 : ℚ) • 1 := by
      ext i j
      simp [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
      ring
    dsimp [S]
    rw [det_fromBlocks_one₁₁,Matrix.one_mul,he,det_smul,det_one,mul_one]
    exact pow_ne_zero _ (by norm_num)
  have he : S * pairedGram a = D * S := by
    dsimp [S,D,pairedGram]
    rw [fromBlocks_multiply,fromBlocks_multiply]
    simp only [Matrix.one_mul,Matrix.mul_one,Matrix.neg_mul,Matrix.mul_neg,
      Matrix.zero_mul,Matrix.mul_zero,neg_zero,add_zero,zero_add]
    congr 1 <;> ext i j
    · change (a * (1 : Matrix R R ℚ) i j + 1) + ((1 : Matrix R R ℚ) i j + 1) =
        (a+1) * (1 : Matrix R R ℚ) i j + 2*1
      ring
    · change ((1 : Matrix R R ℚ) i j + 1) + (a * (1 : Matrix R R ℚ) i j + 1) =
        (a+1) * (1 : Matrix R R ℚ) i j + 2*1
      ring
    · change (a * (1 : Matrix R R ℚ) i j + 1) + -((1 : Matrix R R ℚ) i j + 1) =
        (a-1) * (1 : Matrix R R ℚ) i j
      ring
    · change ((1 : Matrix R R ℚ) i j + 1) + -(a * (1 : Matrix R R ℚ) i j + 1) =
        -((a-1) * (1 : Matrix R R ℚ) i j)
      ring
  have hd : (pairedGram (R := R) a).det = D.det := by
    have hh := congrArg Matrix.det he
    rw [det_mul,det_mul,mul_comm D.det S.det] at hh
    exact mul_left_cancel₀ hs hh
  rw [hd]
  dsimp [D]
  rw [det_fromBlocks_zero₂₁,scalar_ones_det (a+1) ha,det_smul,det_one,mul_one]
  ring

end CoveringDesigns.TwistedArithmetic
