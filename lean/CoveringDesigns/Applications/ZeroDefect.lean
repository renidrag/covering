import CoveringDesigns.Combinatorics.WeightedPartition
import CoveringDesigns.HorsleySingh.LowerBound
import CoveringDesigns.Equality.Slack

/-! Select minimum and next-multiplicity pairs using zero defect and a weighted
partition, then apply the existing Horsley–Singh strict rank obstruction.
Underlying covering argument: Horsley and Singh. Formalisation: Rob Gardiner. -/

namespace CoveringDesigns.Applications.ZeroDefect
open Finset HorsleySingh
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Pairs exactly one above a proposed minimum. -/
def nextPairs (C : Family α) (b₂ : ℕ) : Finset (Finset α) :=
  (pairs α).filter (fun X => multiplicity C X = b₂+1)

/-- Zero defect isolates a minimum pair in the full excess graph. -/
theorem minimum_pair_excess_zero {C : Family α} {k b₂ b₃ b₄ : ℕ}
    (hu : Uniform C k)
    (h₃ : ∀ X : Finset α, X.card = 3 → b₃ ≤ multiplicity C X)
    (h₄ : ∀ X : Finset α, X.card = 4 → b₄ ≤ multiplicity C X)
    (hd : defect (Fintype.card α) k b₂ b₃ b₄ = 0)
    {X Y : Finset α} (hX : X.card = 2) (hm : multiplicity C X = b₂)
    (hY : Y.card = 2) : excess C b₃ b₄ X Y = 0 := by
  have hr := excess_row_sum (b₂ := b₂) (b₃ := b₃) (b₄ := b₄) hu hX
  rw [hm, hd] at hr
  simp only [sub_self, zero_mul, zero_add] at hr
  have hn : ∀ Z ∈ pairs α, 0 ≤ excess C b₃ b₄ X Z :=
    fun Z hZ => excess_nonneg h₃ h₄ hX (mem_pairs.mp hZ)
  have hy := single_le_sum hn (mem_pairs.mpr hY)
  have hz := excess_nonneg h₃ h₄ hX hY
  omega

/-- A large next-multiplicity class can be adjoined to all minimum pairs.
The conclusion is division-free; no pair-minimum attainment is assumed. -/
theorem zero_defect_rank_bound {C : Family α} {k b₂ b₃ b₄ q : ℕ}
    (hu : Uniform C k) (h₄₃ : b₄ ≤ b₃)
    (h₃ : ∀ X : Finset α, X.card = 3 → b₃ ≤ multiplicity C X)
    (h₄ : ∀ X : Finset α, X.card = 4 → b₄ ≤ multiplicity C X)
    (hd : defect (Fintype.card α) k b₂ b₃ b₄ = 0)
    (ha : 0 < diagonal b₂ b₃ b₄) (hq : 0 < q)
    (hpart : ((k.choose 2 : ℤ)-1) / (q : ℤ) < diagonal b₂ b₃ b₄ + 1) :
    q*(minimumPairs C b₂).card + (nextPairs C b₂).card ≤ q*C.card := by
  have hv₀ {X : Finset α} (hX : X ∈ minimumPairs C b₂) :
      X.card = 2 ∧ multiplicity C X = b₂ := by
    simpa only [minimumPairs, mem_filter, mem_pairs] using hX
  have hv₁ {X : Finset α} (hX : X ∈ nextPairs C b₂) :
      X.card = 2 ∧ multiplicity C X = b₂+1 := by
    simpa only [nextPairs, mem_filter, mem_pairs] using hX
  have hn {X Y : Finset α} (hX : X.card = 2) (hY : Y.card = 2) :
      0 ≤ excess C b₃ b₄ X Y := excess_nonneg h₃ h₄ hX hY
  have hiso {X Y : Finset α} (hX : X ∈ minimumPairs C b₂) (hY : Y.card = 2) :
      excess C b₃ b₄ X Y = 0 :=
    minimum_pair_excess_zero hu h₃ h₄ hd (hv₀ hX).1 (hv₀ hX).2 hY
  have hrow (X : Finset α) (hX : X ∈ nextPairs C b₂) :
      ∑ Y ∈ nextPairs C b₂, excess C b₃ b₄ X Y ≤ (k.choose 2 : ℤ)-1 := by
    have hr := excess_row_sum (b₂ := b₂) (b₃ := b₃) (b₄ := b₄) hu (hv₁ hX).1
    rw [(hv₁ hX).2, hd] at hr
    push_cast at hr
    have hs : (∑ Y ∈ nextPairs C b₂, excess C b₃ b₄ X Y) ≤
        ∑ Y ∈ pairs α, excess C b₃ b₄ X Y := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro Y hY _
      exact hn (hv₁ hX).1 (mem_pairs.mp hY)
    linarith
  obtain ⟨T, hT, hcard, hweight⟩ := WeightedPartition.exists_large_subset
    (nextPairs C b₂) hq (excess C b₃ b₄)
    (fun X _ Y _ => excess_comm C b₃ b₄ X Y)
    (fun X _ => by simp [excess]) ((k.choose 2 : ℤ)-1) hrow
  have hdis : Disjoint (minimumPairs C b₂) T := by
    apply disjoint_left.mpr
    intro X hX hXT
    have h₀ := (hv₀ hX).2
    have h₁ := (hv₁ (hT hXT)).2
    omega
  have hs : ∀ X ∈ minimumPairs C b₂ ∪ T, X.card = 2 := by
    intro X hX
    rcases mem_union.mp hX with hX | hX
    · exact (hv₀ hX).1
    · exact (hv₁ (hT hX)).1
  have hrank : (minimumPairs C b₂ ∪ T).card ≤ C.card := by
    apply incidence_rank_obstruction (b₂ := b₂) h₄₃ h₃ h₄ _ hs
    intro X hX
    rcases mem_union.mp hX with hX | hX
    · have hz : ∑ Y ∈ minimumPairs C b₂ ∪ T, excess C b₃ b₄ X Y = 0 :=
        sum_eq_zero (fun Y hY => hiso hX (hs Y hY))
      rw [hz, (hv₀ hX).2]
      simpa using ha
    · rw [sum_union hdis]
      have hz : ∑ Y ∈ minimumPairs C b₂, excess C b₃ b₄ X Y = 0 := by
        apply sum_eq_zero
        intro Y hY
        rw [excess_comm]
        exact hiso hY (hv₁ (hT hX)).1
      rw [hz, zero_add, (hv₁ (hT hX)).2]
      have hh := (hweight X hX).trans_lt hpart
      push_cast
      linarith
  rw [card_union_of_disjoint hdis] at hrank
  have hm := Nat.mul_le_mul_left q hrank
  nlinarith

/-- Convert a weighted count of the two lowest multiplicities into a bound
on the number of blocks. This is counting only, with no matrix assumption.
The exact Equality count retains the coupled contribution of all higher rows. -/
theorem two_level_count {ι : Type*} (S : Finset ι) (u : ι → ℕ)
    {m K b q : ℕ} (hq : 2 ≤ q)
    (hl : ∀ x ∈ S, m ≤ u x) (hs : ∑ x ∈ S, u x = K*b)
    (hr : q*(S.filter (fun x => u x = m)).card +
      (S.filter (fun x => u x = m+1)).card ≤ q*b) :
    (((q : ℤ)-1)*m+q)*S.card ≤ (((q : ℤ)-1)*K+q)*b := by
  classical
  have hp (x : ι) (hx : x ∈ S) :
      1 ≤ (if u x = m then 1 else 0) + (if u x = m+1 then 1 else 0) +
        (u x-(m+1)) := by
    have := hl x hx
    split_ifs <;> omega
  have hc : S.card ≤ (S.filter (fun x => u x = m)).card +
      (S.filter (fun x => u x = m+1)).card + Equality.highExcess S u m := by
    simpa [sum_add_distrib, ← sum_filter, ← card_eq_sum_ones, Equality.highExcess]
      using sum_le_sum hp
  have he := Equality.slack_count hl hs
  have he' : (K : ℤ)*b + (S.filter (fun x => u x = m)).card =
      (S.card : ℤ)*(m+1) + Equality.highExcess S u m := by exact_mod_cast he
  have hc' : (S.card : ℤ) ≤ (S.filter (fun x => u x = m)).card +
      ((S.filter (fun x => u x = m+1)).card : ℤ) + Equality.highExcess S u m := by
    exact_mod_cast hc
  have hr' : (q : ℤ)*(S.filter (fun x => u x = m)).card +
      (S.filter (fun x => u x = m+1)).card ≤ (q : ℤ)*b := by exact_mod_cast hr
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hh := mul_nonneg (show 0 ≤ (q : ℤ)-2 by omega)
    (Int.natCast_nonneg (Equality.highExcess S u m))
  have heq := congrArg (fun z : ℤ => ((q : ℤ)-1)*z) he'
  nlinarith only [heq, hc', hr', hh]

end CoveringDesigns.Applications.ZeroDefect
