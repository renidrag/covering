import CoveringDesigns.MulticoverIncidence.LowerBound
import CoveringDesigns.Multicover.Family
import CoveringDesigns.HigherIncidence.LowerBound

/-! Multiplicity-one compatibility, including the universal smaller-cover bounds.
Deduplication is used only in this adapter, never for higher multiplicity. -/
namespace CoveringDesigns.MulticoverIncidence
open Finset HigherIncidence
universe u w

/-- An ordinary universal bound also bounds indexed multiplicity-one covers. -/
theorem coverLower_of_family {v k t m : ℕ}
    (h : HorsleySingh.CoverLower.{u} v k t m) :
    Multicover.CoverLower.{u,w} v k t 1 m := by
  intro α ι _ _ _ B hn hc
  exact (h hn ((Multicover.deduplicate_isCover_one B k t).mpr hc)).trans
    (Multicover.deduplicate_card_le B)

theorem coverLower_one_iff {v k t m : ℕ} :
    Multicover.CoverLower.{u,u} v k t 1 m ↔ HorsleySingh.CoverLower.{u} v k t m := by
  constructor
  · intro h α _ _ C hn hc
    simpa only [Multicover.ofFamily_card] using
      h hn ((Multicover.ofFamily_isCover_one C k t).mpr hc)
  · exact coverLower_of_family

theorem parameters_one_iff {v k t s : ℕ} {b : ℕ → ℕ} :
    Parameters 1 v k t s b ↔ HigherIncidence.Parameters v k t s b := by
  constructor
  · exact Parameters.toOrdinary
  · intro h
    refine ⟨by omega, h.order_pos, h.strength, h.strength_lt, h.block_lt,
      h.positive, ?_, h.step, h.coefficients⟩
    simpa only [Multicover.bound_one_eq] using h.seed

theorem smallerBounds_of_family {v k t s : ℕ} {b : ℕ → ℕ}
    (h : HigherIncidence.SmallerBounds.{u} v k t s b) :
    SmallerBounds.{u,w} 1 v k t s b :=
  fun i hlo hhi => coverLower_of_family (h i hlo hhi)

theorem smallerBounds_one_iff {v k t s : ℕ} {b : ℕ → ℕ} :
    SmallerBounds.{u,u} 1 v k t s b ↔ HigherIncidence.SmallerBounds.{u} v k t s b := by
  constructor
  · intro h i hlo hhi
    exact coverLower_one_iff.mp (h i hlo hhi)
  · exact smallerBounds_of_family

theorem bound_eq_ordinary (v k s : ℕ) (b : ℕ → ℕ) :
    bound v k s b = HigherIncidence.bound v k s b := rfl

variable {α : Type u} [DecidableEq α]

theorem incidence_ofFamily (C : Family α) (S : Finset (Finset α)) :
    incidence (Multicover.ofFamily C) S = HorsleySingh.incidence C S := rfl

theorem excess_ofFamily (C : Family α) (b : ℕ → ℕ) (X Y : Finset α) :
    excess (Multicover.ofFamily C) b X Y = HigherIncidence.excess C b X Y := by
  simp only [excess, HigherIncidence.excess, Multicover.ofFamily_subsetDegree]

/-- The ordinary Theorem 6 contract recovered through indexed occurrences. -/
theorem family_lower_bound [Fintype α] {C : Family α} {v k t s : ℕ} {b : ℕ → ℕ}
    (hp : HigherIncidence.Parameters v k t s b)
    (hb : HigherIncidence.SmallerBounds.{u} v k t s b)
    (hn : Fintype.card α=v) (h : CoveringDesigns.IsCover C k t)
    (hd : defect v k s b < coefficient s b s) : HigherIncidence.bound v k s b ≤ C.card := by
  simpa only [bound_eq_ordinary, Multicover.ofFamily_card] using
    lower_bound (parameters_one_iff.mpr hp) (smallerBounds_of_family hb) hn
      ((Multicover.ofFamily_isCover_one C k t).mpr h) hd

end CoveringDesigns.MulticoverIncidence
