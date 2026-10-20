import CoveringDesigns.AffineCapacity.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Binary points in an affine space

Splitting at a varying coordinate partitions the actual binary vectors
into two fibres. Differences within either fibre lie in a proper
coordinate kernel, dropping dimension. Induction gives `2^d`, including
empty selections and dimension zero. This is the coordinate-projection
argument in an inductive form; it does not enumerate configurations.
-/

namespace CoveringDesigns.AffineCapacity

open Finset Module

variable {ι : Type*} [Fintype ι]

private theorem binary_card_aux (d : ℕ) :
    ∀ (W : Submodule ℝ (ι → ℝ)), finrank ℝ W ≤ d →
    ∀ (S : Finset (ι → ℝ)),
      (∀ x ∈ S, ∀ i, x i = 0 ∨ x i = 1) →
      (∀ x ∈ S, ∀ y ∈ S, x - y ∈ W) → S.card ≤ 2 ^ d := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro W hW S hbin hdiff
    by_cases hsmall : S.card ≤ 1
    · exact hsmall.trans (Nat.one_le_pow d 2 (by omega))
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (by omega : 1 < S.card)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    let U : Submodule ℝ (ι → ℝ) := W ⊓ LinearMap.ker (LinearMap.proj i)
    have hlt : U < W := by
      refine lt_iff_le_and_ne.mpr ⟨inf_le_left, ?_⟩
      intro he
      have hm : x - y ∈ U := he ▸ hdiff x hx y hy
      have hz : x i - y i = 0 := hm.2
      exact hi (sub_eq_zero.mp hz)
    have hdim := Submodule.finrank_lt_finrank_of_lt hlt
    have hud : finrank ℝ U < d := lt_of_lt_of_le hdim hW
    let S₀ := S.filter fun x => x i = 0
    let S₁ := S.filter fun x => x i = 1
    have hpart : S₀ ∪ S₁ = S := by
      ext z
      simp only [S₀, S₁, mem_union, mem_filter]
      constructor
      · tauto
      · intro hz
        rcases hbin z hz i with h0 | h1
        · exact Or.inl ⟨hz, h0⟩
        · exact Or.inr ⟨hz, h1⟩
    have hdisj : Disjoint S₀ S₁ := by
      apply disjoint_left.mpr
      intro z hz0 hz1
      have h0 := (mem_filter.mp hz0).2
      have h1 := (mem_filter.mp hz1).2
      norm_num [h0] at h1
    have hcap (c : ℝ) :
        (S.filter fun z => z i = c).card ≤ 2 ^ finrank ℝ U := by
      apply ih (finrank ℝ U) hud U le_rfl
      · intro z hz
        exact hbin z (mem_filter.mp hz).1
      · intro z hz q hq
        refine ⟨hdiff z (mem_filter.mp hz).1 q (mem_filter.mp hq).1, ?_⟩
        change z i - q i = 0
        rw [(mem_filter.mp hz).2, (mem_filter.mp hq).2, sub_self]
    calc
      S.card = S₀.card + S₁.card := by rw [← card_union_of_disjoint hdisj, hpart]
      _ ≤ 2 ^ finrank ℝ U + 2 ^ finrank ℝ U := Nat.add_le_add (hcap 0) (hcap 1)
      _ = 2 ^ (finrank ℝ U + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) (by omega)

/-- Binary vectors whose differences lie in a d-dimensional subspace
number at most `2^d`. No nonempty premise is required. -/
theorem binary_card_le_pow (W : Submodule ℝ (ι → ℝ))
    (S : Finset (ι → ℝ))
    (hbin : ∀ x ∈ S, ∀ i, x i = 0 ∨ x i = 1)
    (hdiff : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ W) :
    S.card ≤ 2 ^ finrank ℝ W :=
  binary_card_aux _ W le_rfl S hbin hdiff

/-- A finite selection of binary vectors in a real affine space is bounded
by the dimension of that space's direction. Empty affine spaces are allowed. -/
theorem binary_affine_card_le_pow (A : AffineSubspace ℝ (ι → ℝ))
    (S : Finset (ι → ℝ)) (hS : (S : Set (ι → ℝ)) ⊆ A)
    (hbin : ∀ x ∈ S, ∀ i, x i = 0 ∨ x i = 1) :
    S.card ≤ 2 ^ finrank ℝ A.direction := by
  apply binary_card_le_pow A.direction S hbin
  intro x hx y hy
  exact A.vsub_mem_direction (hS hx) (hS hy)

end CoveringDesigns.AffineCapacity
