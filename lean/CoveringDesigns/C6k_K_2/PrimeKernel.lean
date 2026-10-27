import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Matrix.Mul

/-! Integer lifts modulo `p²` force a modular kernel to be isotropic. -/

open Matrix
open scoped BigOperators

namespace CoveringDesigns.C6k_K_2

private theorem prime_cancel {p : ℕ} (hp : Nat.Prime p) {a d : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (h : (p : ℤ)^2 ∣ (p : ℤ)*a*d) : (p : ℤ) ∣ d := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd : (p : ℤ) ∣ a*d := (Int.mul_dvd_mul_iff_left hpz).mp
    (by simpa [pow_two, mul_assoc] using h)
  exact ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hd).resolve_left ha

private theorem gram_pairing {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    (B : Matrix S T ℤ) (c : ℤ)
    (hgram : B.transpose * B = c • 1 + Matrix.of (fun (_ _ : T) => (1 : ℤ)))
    (X Y : T → ℤ) :
    (B *ᵥ X) ⬝ᵥ (B *ᵥ Y) = c * (X ⬝ᵥ Y) + (∑ t, X t) * (∑ t, Y t) := by
  calc
    (B *ᵥ X) ⬝ᵥ (B *ᵥ Y) = X ⬝ᵥ ((B.transpose * B) *ᵥ Y) := by
      rw [← mulVec_mulVec, dotProduct_mulVec X, vecMul_transpose]
    _ = c * (X ⬝ᵥ Y) + (∑ t, X t) * (∑ t, Y t) := by
      rw [hgram, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul]
      simp [mulVec, dotProduct, Finset.sum_mul, mul_comm]

private theorem lift_sum_dvd {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    {p : ℕ} [Fact (Nat.Prime p)] (B : Matrix S T ℤ) (a : ℤ)
    (hgram : B.transpose * B = ((p : ℤ)*a) • 1 + Matrix.of (fun (_ _ : T) => (1 : ℤ)))
    (X : T → ℤ)
    (hX : (Int.castRingHom (ZMod p)) ∘ (B *ᵥ X) = 0) :
    (p : ℤ) ∣ ∑ t, X t := by
  classical
  cases isEmpty_or_nonempty T with
  | inl h => simp
  | inr h =>
    let t : T := Classical.choice h
    let f := Int.castRingHom (ZMod p)
    have hz : f (((B.transpose * B) *ᵥ X) t) = 0 := by
      rw [← mulVec_mulVec, f.map_mulVec, hX, mulVec_zero, Pi.zero_apply]
    rw [hgram, add_mulVec, smul_mulVec, one_mulVec] at hz
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct] using hz

/-- For an arbitrary rectangular integer matrix with Gram matrix `pa I + J`,
`p ∤ a` makes its kernel modulo the prime `p` totally isotropic. -/
theorem kernel_totally_isotropic
    {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    {p : ℕ} [Fact (Nat.Prime p)] {a : ℤ}
    (B : Matrix S T ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (hgram : B.transpose * B = ((p : ℤ)*a) • 1 + Matrix.of (fun (_ _ : T) => (1 : ℤ)))
    (x y : T → ZMod p)
    (hx : (B.map (Int.castRingHom (ZMod p))) *ᵥ x = 0)
    (hy : (B.map (Int.castRingHom (ZMod p))) *ᵥ y = 0) : x ⬝ᵥ y = 0 := by
  classical
  let f := Int.castRingHom (ZMod p)
  let X : T → ℤ := fun t => (x t).cast
  let Y : T → ℤ := fun t => (y t).cast
  have hX : f ∘ X = x := by funext t; exact ZMod.intCast_zmod_cast _
  have hY : f ∘ Y = y := by funext t; exact ZMod.intCast_zmod_cast _
  have hBX : f ∘ (B *ᵥ X) = 0 := by
    funext s
    change f ((B *ᵥ X) s) = 0
    rw [f.map_mulVec, hX]
    exact congrFun hx s
  have hBY : f ∘ (B *ᵥ Y) = 0 := by
    funext s
    change f ((B *ᵥ Y) s) = 0
    rw [f.map_mulVec, hY]
    exact congrFun hy s
  have hdX : ∀ s, (p : ℤ) ∣ (B *ᵥ X) s := fun s =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hBX s)
  have hdY : ∀ s, (p : ℤ) ∣ (B *ᵥ Y) s := fun s =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hBY s)
  have hpair : (p : ℤ)^2 ∣ (B *ᵥ X) ⬝ᵥ (B *ᵥ Y) := by
    apply Finset.dvd_sum
    intro s _
    simpa only [pow_two] using mul_dvd_mul (hdX s) (hdY s)
  have hsum : (p : ℤ)^2 ∣ (∑ t, X t) * (∑ t, Y t) := by
    simpa only [pow_two] using mul_dvd_mul
      (lift_sum_dvd B a hgram X hBX) (lift_sum_dvd B a hgram Y hBY)
  rw [gram_pairing B ((p : ℤ)*a) hgram X Y] at hpair
  have hd : (p : ℤ) ∣ X ⬝ᵥ Y :=
    prime_cancel Fact.out ha (by simpa using dvd_sub hpair hsum)
  have hz : f (X ⬝ᵥ Y) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  simpa only [f.map_dotProduct, hX, hY] using hz

end CoveringDesigns.C6k_K_2
