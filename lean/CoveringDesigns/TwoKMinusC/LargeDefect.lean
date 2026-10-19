import CoveringDesigns.TwoKMinusC.Algebra
import CoveringDesigns.Multicover.Family

/-! Ordinary actual-family adapter, independent of any saturation or threshold
theorem. Floors belong to this family, not to universal residual coverings.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusC
open Finset HigherIncidence
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem actual_subset_floors {C : Family α}
    (hpoint : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (Z : Finset α) (hlo : 1 ≤ Z.card) (hhi : Z.card ≤ 2) :
    seed Z.card ≤ indexedSubsetDegree (Multicover.ofFamily C) Z := by
  rcases (show Z.card=1 ∨ Z.card=2 by omega) with h | h
  · obtain ⟨x,rfl⟩ := card_eq_one.mp h
    simpa [seed, Multicover.subsetDegree_singleton, Multicover.ofFamily_degree]
      using hpoint x
  · obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp h
    rw [Multicover.ofFamily_subsetDegree]
    simpa [seed, hxy, HorsleySingh.multiplicity, degree, star, filter_filter,
      insert_subset_iff, singleton_subset_iff] using hpair x y hxy

theorem actual_floors_bound {C : Family α} {c k : ℕ}
    (hv : Fintype.card α+c=2*k) (hc : 2≤c) (hck : c<k) (hk : 6<k)
    (hu : Uniform C k) (hpoint : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    Nat.ceil (Q c k) ≤ C.card := by
  have hd := offsetDefect_ge hc
  have hb := MulticoverLargeDefect.lower_bound_of_multiplicities
    ((Multicover.ofFamily_uniform C k).mpr hu)
    (s := 1) (b := seed)
    (by
      intro j hj
      have hj0 : j=0 := by omega
      subst j
      rw [coefficient_zero]
      norm_num)
    (by intro Z hlo hhi; exact actual_subset_floors hpoint hpair Z hlo hhi)
    (by simpa [seed] using hk)
    (by rw [coefficient_one]; norm_num [seed])
    (by rw [coefficient_one]; norm_num)
    (by rw [coefficient_one, defect_eq hv hck]; exact hd)
  simpa only [MulticoverLargeDefect.bound, value_eq_Q hv hc hck,
    Multicover.ofFamily_card] using hb

theorem actual_floors_real {C : Family α} {c k : ℕ}
    (hv : Fintype.card α+c=2*k) (hc : 2≤c) (hck : c<k) (hk : 6<k)
    (hu : Uniform C k) (hpoint : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    Q c k ≤ (C.card : ℝ) :=
  Nat.ceil_le.mp (actual_floors_bound hv hc hck hk hu hpoint hpair)

theorem actual_floors_inequality {C : Family α} {c k : ℕ}
    (hv : Fintype.card α+c=2*k) (hc : 2≤c) (hck : c<k) (hk : 6<k)
    (hu : Uniform C k) (hpoint : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    numerator c k ≤ (C.card : ℝ)*denominator c k :=
  (Q_le_iff hc).mp (actual_floors_real hv hc hck hk hu hpoint hpair)

end CoveringDesigns.TwoKMinusC
