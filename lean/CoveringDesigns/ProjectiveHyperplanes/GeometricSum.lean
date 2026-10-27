import CoveringDesigns.AffineSchoenheim.Arithmetic

/-! Geometric-sum helpers for projective hyperplanes. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.ProjectiveHyperplanes
open AffineSchoenheim

/-- The existing finite geometric sum, including G(q,0)=0. -/
abbrev G := AffineSchoenheim.geom

theorem index_le_geom {q : ℕ} (hq : 1 ≤ q) (n : ℕ) : n ≤ G q n := by
  induction n with
  | zero => simp [G]
  | succ n ih =>
    rw [G, geom_succ]
    have := Nat.mul_le_mul_right (G q n) hq
    change n + 1 ≤ q * G q n + 1
    nlinarith

theorem geom_le_succ {q : ℕ} (hq : 1 ≤ q) (n : ℕ) : G q n ≤ G q (n+1) := by
  rw [G, geom_succ]
  have := Nat.mul_le_mul_right (G q n) hq
  change G q n ≤ q * G q n + 1
  nlinarith

theorem geom_add (q a b : ℕ) : G q (a+b) = G q a + q^a * G q b := by
  induction b with
  | zero => simp [G]
  | succ b ih =>
    rw [show a + (b+1) = (a+b)+1 by omega, G, geom_succ]
    change q * G q (a+b) + 1 = G q a + q^a * G q (b+1)
    rw [ih, G, geom_succ]
    -- Use the last-term identity, valid also at q=0.
    have he : G q (a+1) = G q a + q^a := by
      simp [G, geom, Finset.sum_range_succ]
    have he' := geom_succ q a
    change G q (a+1) = q * G q a + 1 at he'
    nlinarith only [he, he']

theorem bernoulli_nat {q : ℕ} (hq : 1 ≤ q) (j : ℕ) :
    1 + j*(q-1) ≤ q^j := by
  have he := geom_mul_add hq j
  have hm := Nat.mul_le_mul_left (q-1) (index_le_geom hq j)
  nlinarith only [he, hm]

end CoveringDesigns.ProjectiveHyperplanes
