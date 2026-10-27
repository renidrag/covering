import CoveringDesigns.AffineConstructions.Construction
import Mathlib.Tactic.NormNum

/-! Fixed existential construction checks; no exact-value or novelty claims. -/

namespace CoveringDesigns.AffineConstructions.Examples

theorem four_prime_power : IsPrimePow (4 : ℕ) :=
  (isPrimePow_nat_iff 4).mpr ⟨2, 2, Nat.prime_two, by decide, by norm_num⟩

theorem upper_bound_9_3_2 {α : Type*} [Fintype α] (hn : Fintype.card α = 9) :
    ∃ C : Family α, IsCover C 3 2 ∧ C.card ≤ 12 := by
  simpa [blockBound] using lemma8 (q := 3) (m := 1) (t := 2)
    Nat.prime_three.isPrimePow (by decide) (by decide)
    hn (by norm_num) (by norm_num)

theorem upper_bound_16_4_2 {α : Type*} [Fintype α] (hn : Fintype.card α = 16) :
    ∃ C : Family α, IsCover C 4 2 ∧ C.card ≤ 20 := by
  simpa [blockBound] using lemma8 (q := 4) (m := 1) (t := 2)
    four_prime_power (by decide) (by decide) hn (by norm_num) (by norm_num)

theorem upper_bound_8_4_3 {α : Type*} [Fintype α] (hn : Fintype.card α = 8) :
    ∃ C : Family α, IsCover C 4 3 ∧ C.card ≤ 14 := by
  simpa [blockBound] using lemma8 (q := 2) (m := 1) (t := 3)
    Nat.prime_two.isPrimePow (by decide) (by decide) hn (by norm_num) (by norm_num)

theorem upper_bound_17_6_2 {α : Type*} [Fintype α] (hn : Fintype.card α = 17) :
    ∃ C : Family α, IsCover C 6 2 ∧ C.card ≤ 12 := by
  simpa [blockBound] using lemma8 (q := 3) (m := 2) (t := 2)
    Nat.prime_three.isPrimePow (by decide) (by decide)
    hn (by norm_num) (by norm_num)

theorem strength_one {α : Type*} [Fintype α] {q m v : ℕ}
    (hq : IsPrimePow q) (hm : 0 < m) (hn : Fintype.card α = v)
    (hl : m ≤ v) (hu : v ≤ m*q) :
    ∃ C : Family α, IsCover C m 1 ∧ C.card ≤ q := by
  simpa [blockBound, Nat.div_self (denominator_pos hq)] using
    lemma8 (t := 1) hq hm (by decide) hn (by simpa using hl) (by simpa using hu)

theorem no_blow_up {α : Type*} [Fintype α] {q t : ℕ}
    (hq : IsPrimePow q) (ht : 0 < t) (hn : Fintype.card α = q^t) :
    ∃ C : Family α, IsCover C (q^(t-1)) t ∧ C.card ≤ blockBound q t := by
  simpa using lemma8 (m := 1) hq (by decide) ht hn
    (by simpa using block_size_le_points (m := 1) (t := t) hq) (by simp)

theorem lower_endpoint {α : Type*} [Fintype α] {q m t : ℕ}
    (hq : IsPrimePow q) (hm : 0 < m) (ht : 0 < t)
    (hn : Fintype.card α = m*q^(t-1)) :
    ∃ C : Family α, IsCover C (m*q^(t-1)) t ∧ C.card ≤ blockBound q t :=
  lemma8 hq hm ht hn le_rfl (block_size_le_points hq)

theorem upper_endpoint {α : Type*} [Fintype α] {q m t : ℕ}
    (hq : IsPrimePow q) (hm : 0 < m) (ht : 0 < t)
    (hn : Fintype.card α = m*q^t) :
    ∃ C : Family α, IsCover C (m*q^(t-1)) t ∧ C.card ≤ blockBound q t :=
  lemma8 hq hm ht hn (block_size_le_points hq) le_rfl

/-- Index multiplicity is not distinct-block multiplicity. -/
theorem duplicate_blocks_collapse :
    ((Finset.univ : Finset (Fin 3)).image
      (fun _ => (Finset.univ : Finset (Fin 2)))).card = 1 := by
  rw [Finset.image_const (by simp) _, Finset.card_singleton]

end CoveringDesigns.AffineConstructions.Examples
