import CoveringDesigns.Equality.Slack
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp

/-! General finite-row accounting behind Horsley–Singh Lemma 13.
No incidence, rank or covering hypothesis is built into these statements.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.Weighted
open Finset
variable {ι : Type*}

/-- Every row is low, next-low, or contributes at least one unit to high excess. -/
theorem card_le_two_levels_add_highExcess (S : Finset ι) (u : ι → ℕ) {m : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) :
    S.card ≤ (S.filter (fun x => u x = m)).card +
      (S.filter (fun x => u x = m+1)).card + Equality.highExcess S u m := by
  classical
  have hp (x : ι) (hx : x ∈ S) :
      1 ≤ (if u x = m then 1 else 0) + (if u x = m+1 then 1 else 0) +
        (u x-(m+1)) := by
    have := hl x hx
    split_ifs <;> omega
  simpa [sum_add_distrib, ← sum_filter, ← card_eq_sum_ones, Equality.highExcess]
    using sum_le_sum hp

/-- The division-free weighted two-level bound. All coefficient subtraction
and multiplication in the conclusion take place in the reals. -/
theorem two_level_bound (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {α β : ℝ}
    (hβ : 0 ≤ β) (hα : 2*β ≤ α)
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : α * (S.filter (fun x => u x = m)).card +
      β * (S.filter (fun x => u x = m+1)).card ≤ b) :
    (S.card : ℝ) * ((m : ℝ)*(α-β)+α) ≤ (b : ℝ)*((K : ℝ)*(α-β)+1) := by
  have he : (K : ℝ)*b + (S.filter (fun x => u x = m)).card =
      (S.card : ℝ)*(m+1) + Equality.highExcess S u m := by
    exact_mod_cast Equality.slack_count hl hs
  have hc : (S.card : ℝ) ≤ (S.filter (fun x => u x = m)).card +
      ((S.filter (fun x => u x = m+1)).card : ℝ) + Equality.highExcess S u m := by
    exact_mod_cast card_le_two_levels_add_highExcess S u hl
  have heq := congrArg (fun z : ℝ => (α-β)*z) he
  have hcβ := mul_le_mul_of_nonneg_left hc hβ
  have hh := mul_nonneg (sub_nonneg.mpr hα)
    (Nat.cast_nonneg (Equality.highExcess S u m) : (0 : ℝ) ≤ _)
  nlinarith only [heq, hcβ, hh, hr]

/-- The denominator is strictly positive even when K or both coefficients vanish. -/
theorem two_level_denominator_pos (K : ℕ) {α β : ℝ}
    (hβ : 0 ≤ β) (hα : 2*β ≤ α) : 0 < (K : ℝ)*(α-β)+1 := by
  have hd : 0 ≤ α-β := by linarith
  have := mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) hd
  linarith

theorem two_level_ratio (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {α β : ℝ}
    (hβ : 0 ≤ β) (hα : 2*β ≤ α)
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : α * (S.filter (fun x => u x = m)).card +
      β * (S.filter (fun x => u x = m+1)).card ≤ b) :
    (S.card : ℝ) * ((m : ℝ)*(α-β)+α) / ((K : ℝ)*(α-β)+1) ≤ b :=
  (div_le_iff₀ (two_level_denominator_pos K hβ hα)).mpr
    (two_level_bound S u hβ hα hl hs hr)

/-- Natural ceiling of the real ratio; no numerical approximation is involved. -/
theorem two_level_ceiling (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {α β : ℝ}
    (hβ : 0 ≤ β) (hα : 2*β ≤ α)
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : α * (S.filter (fun x => u x = m)).card +
      β * (S.filter (fun x => u x = m+1)).card ≤ b) :
    ⌈(S.card : ℝ) * ((m : ℝ)*(α-β)+α) / ((K : ℝ)*(α-β)+1)⌉₊ ≤ b :=
  Nat.ceil_le.mpr (two_level_ratio S u hβ hα hl hs hr)

/-- Taking alpha=1 and beta=1/q recovers the integer q-weighted inequality.
This proof imports no ZeroDefect application. -/
theorem two_level_q (S : Finset ι) (u : ι → ℕ) {m K b q : ℕ} (hq : 2 ≤ q)
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : q*(S.filter (fun x => u x = m)).card +
      (S.filter (fun x => u x = m+1)).card ≤ q*b) :
    (S.card : ℤ)*(((q : ℤ)-1)*m+q) ≤ (b : ℤ)*(((q : ℤ)-1)*K+q) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have ha : 2*(1/(q : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_iff₀ hqp]
    linarith
  have hr' : (1 : ℝ)*(S.filter (fun x => u x = m)).card +
      (1/(q : ℝ))*(S.filter (fun x => u x = m+1)).card ≤ b := by
    apply (mul_le_mul_iff_of_pos_left hqp).mp
    have he : (q : ℝ) * (1*(S.filter (fun x => u x = m)).card +
        (1/(q : ℝ))*(S.filter (fun x => u x = m+1)).card) =
        (q : ℝ)*(S.filter (fun x => u x = m)).card +
          (S.filter (fun x => u x = m+1)).card := by
      field_simp
    rw [he]
    exact_mod_cast hr
  have hc := two_level_bound S u (by positivity : (0 : ℝ) ≤ 1/(q : ℝ)) ha hl hs hr'
  have hm := mul_le_mul_of_nonneg_left hc hqp.le
  have he (n r : ℕ) : (q : ℝ)*((r : ℝ)*((n : ℝ)*(1-1/(q : ℝ))+1)) =
      (r : ℝ)*(((q : ℝ)-1)*n+q) := by
    field_simp
  rw [he m S.card, he K b] at hm
  exact_mod_cast hm

end CoveringDesigns.Weighted
