import CoveringDesigns.Equality.FiniteSum

/-! The counting part of Horsley's slack, separated from the rank obstruction. -/
namespace CoveringDesigns.Equality
open Finset
variable {ι : Type*}

/-- Excess beyond the two lowest multiplicities. Natural subtraction is intentional. -/
def highExcess (S : Finset ι) (u : ι → ℕ) (m : ℕ) : ℕ :=
  ∑ x ∈ S, (u x - (m+1))

/-- Signed slack in the unrounded Horsley inequality. -/
def slack (N K b m : ℕ) : ℤ := (K+1 : ℕ) * (b : ℤ) - (N : ℤ) * (m+1 : ℕ)

/-- The exact additive count; no rank hypothesis. -/
theorem slack_count {S : Finset ι} {u : ι → ℕ} {m K b : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b) :
    K*b + (S.filter (fun x => u x = m)).card = S.card*(m+1) + highExcess S u m := by
  have hp (x : ι) (hx : x ∈ S) :
      u x + (if u x = m then 1 else 0) = (m+1) + (u x-(m+1)) := by
    have := hl x hx
    split_ifs <;> omega
  have he := sum_congr rfl hp
  have hm : (∑ x ∈ S, if u x = m then 1 else 0) =
      (S.filter (fun x => u x = m)).card := by
    simp only [card_eq_sum_ones, sum_filter]
  simpa only [sum_add_distrib, hs, hm, sum_const, nsmul_eq_mul, highExcess, Nat.cast_id, mul_add] using he

/-- Exact signed slack decomposition, before any rank assumption. -/
theorem slack_identity {S : Finset ι} {u : ι → ℕ} {m K b : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b) :
    slack S.card K b m = ((b : ℤ) - (S.filter (fun x => u x = m)).card) +
      highExcess S u m := by
  have hz := congrArg (fun n : ℕ => (n : ℤ)) (slack_count hl hs)
  push_cast at hz
  unfold slack
  push_cast
  nlinarith

/-- The rank condition gives the lower bounds on both slack summands. -/
theorem slack_summands_nonneg {S : Finset ι} {u : ι → ℕ} {m b : ℕ}
    (hr : (S.filter (fun x => u x = m)).card ≤ b) :
    0 ≤ (b : ℤ) - (S.filter (fun x => u x = m)).card ∧
      0 ≤ (highExcess S u m : ℤ) := by
  omega

/-- Rank makes both summands nonnegative and bounds each by the total slack. -/
theorem slack_bounds {S : Finset ι} {u : ι → ℕ} {m K b : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : (S.filter (fun x => u x = m)).card ≤ b) :
    0 ≤ slack S.card K b m ∧
      (b : ℤ) - (S.filter (fun x => u x = m)).card ≤ slack S.card K b m ∧
      (highExcess S u m : ℤ) ≤ slack S.card K b m := by
  rw [slack_identity hl hs]
  omega

theorem high_excess_zero {S : Finset ι} {u : ι → ℕ} {m : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) (he : highExcess S u m = 0) :
    ∀ x ∈ S, u x = m ∨ u x = m+1 := by
  intro x hx
  have := budget_zero he x hx
  have := hl x hx
  omega

theorem high_excess_one {S : Finset ι} {u : ι → ℕ} {m : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) (he : highExcess S u m = 1) :
    ∃ p ∈ S, u p = m+2 ∧ ∀ q ∈ S, q ≠ p → u q = m ∨ u q = m+1 := by
  obtain ⟨p, hp, he, hq⟩ := budget_one he
  refine ⟨p, hp, by omega, ?_⟩
  intro q hqS hqp
  have := hq q hqS hqp
  have := hl q hqS
  omega

theorem slack_zero {S : Finset ι} {u : ι → ℕ} {m K b : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : (S.filter (fun x => u x = m)).card ≤ b)
    (he : slack S.card K b m = 0) :
    (S.filter (fun x => u x = m)).card = b ∧
      ∀ x ∈ S, u x = m ∨ u x = m+1 := by
  have hi := slack_identity hl hs
  have hz : highExcess S u m = 0 := by omega
  exact ⟨by omega, high_excess_zero hl hz⟩

theorem slack_one {S : Finset ι} {u : ι → ℕ} {m K b : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : (S.filter (fun x => u x = m)).card ≤ b)
    (he : slack S.card K b m = 1) :
    ((S.filter (fun x => u x = m)).card + 1 = b ∧ highExcess S u m = 0 ∧
      ∀ x ∈ S, u x = m ∨ u x = m+1) ∨
    ((S.filter (fun x => u x = m)).card = b ∧ highExcess S u m = 1 ∧
      ∃ p ∈ S, u p = m+2 ∧ ∀ q ∈ S, q ≠ p → u q = m ∨ u q = m+1) := by
  have hi := slack_identity hl hs
  by_cases hz : highExcess S u m = 0
  · exact Or.inl ⟨by omega, hz, high_excess_zero hl hz⟩
  · have ho : highExcess S u m = 1 := by omega
    exact Or.inr ⟨by omega, ho, high_excess_one hl ho⟩

/-- Each row at least two above the minimum consumes at least one slack unit. -/
theorem slack_high_count {S : Finset ι} {u : ι → ℕ} {m K b : ℕ}
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : (S.filter (fun x => u x = m)).card ≤ b) :
    ((S.filter (fun x => m+2 ≤ u x)).card : ℤ) ≤ slack S.card K b m := by
  have hc : (S.filter (fun x => m+2 ≤ u x)).card ≤ highExcess S u m := by
    have he : S.filter (fun x => m+2 ≤ u x) = S.filter (fun x => 1 ≤ u x-(m+1)) := by
      ext x
      simp only [mem_filter]
      constructor <;> rintro ⟨hx, hh⟩ <;> exact ⟨hx, by omega⟩
    rw [he]
    simpa only [one_mul, highExcess] using threshold_count_le S (fun x => u x-(m+1)) 1
  have hi : ((S.filter (fun x => m+2 ≤ u x)).card : ℤ) ≤ highExcess S u m := by
    exact_mod_cast hc
  exact hi.trans (slack_bounds hl hs hr).2.2

end CoveringDesigns.Equality
