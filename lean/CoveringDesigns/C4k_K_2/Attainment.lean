import CoveringDesigns.C4k_K_2.Barker
import CoveringDesigns.PairConstructions.Weighted
import CoveringDesigns.AffineConstructions.Examples

namespace CoveringDesigns.C4k_K_2

private theorem weighted_parameters {k : ℕ} (hk : 8 ≤ k) (hnd : ¬ 4 ∣ k)
    (hne : k ≠ 11) : ∃ u r : ℕ, 1 ≤ r ∧ r ≤ 3 ∧ r ≤ u ∧ k = 4*u+r := by
  have hm : k % 4 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hnd
  refine ⟨k/4,k%4,?_,?_,?_,?_⟩ <;> omega

/-- The affine expansion budget for k divisible by four. -/
theorem affine_attainment {α : Type*} [Fintype α] {k : ℕ}
    (hk : 4 ≤ k) (hv : Fintype.card α = 4*k) (hd : 4 ∣ k) :
    ∃ C : Family α, IsCover C k 2 ∧ C.card ≤ 20 := by
  obtain ⟨u,rfl⟩ := hd
  have hu : 0 < u := by omega
  obtain ⟨C,hC,hb⟩ := AffineConstructions.lemma8 (q := 4) (m := u) (t := 2)
    AffineConstructions.Examples.four_prime_power hu (by decide) hv
    (by norm_num; omega) (by norm_num; omega)
  refine ⟨C,?_,?_⟩
  · simpa [Nat.mul_comm] using hC
  · simpa [AffineConstructions.blockBound] using hb

/-- Actual ordinary attainment budgets, including the retained exceptional witness. -/
theorem upper_bound {α : Type*} [Fintype α] {k : ℕ}
    (hk : 8 ≤ k) (hv : Fintype.card α = 4*k) :
    ∃ C : Family α, IsCover C k 2 ∧ C.card ≤ (if 4 ∣ k then 20 else 21) := by
  by_cases hd : 4 ∣ k
  · simpa [hd] using affine_attainment (by omega : 4 ≤ k) hv hd
  · rw [if_neg hd]
    by_cases he : k = 11
    · subst k
      obtain ⟨C,hC,hb⟩ := Barker.attainment (by simpa using hv)
      exact ⟨C,hC,hb.le⟩
    · obtain ⟨u,r,hr,_,hru,hk⟩ := weighted_parameters hk hd he
      subst k
      simpa using PairConstructions.weighted_projective
        AffineConstructions.Examples.four_prime_power (by decide) hr hru hv

end CoveringDesigns.C4k_K_2
