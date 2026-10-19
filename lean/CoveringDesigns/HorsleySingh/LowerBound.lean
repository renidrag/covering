import CoveringDesigns.HorsleySingh.Matrices
import CoveringDesigns.HorsleySingh.Parameters

/-! The ordinary-covering, s = 2 specialisation of Horsley–Singh Theorem 6.
The theorem and structural argument are due to Horsley and Singh.
Formalisation credit: Rob Gardiner. -/

namespace CoveringDesigns.HorsleySingh

open Finset
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

def bound (v k b₂ : ℕ) : ℕ :=
  Schoenheim.ceilDiv (v.choose 2 * (b₂+1)) (k.choose 2 + 1)

/-- Pairs having the assumed minimum multiplicity. -/
def minimumPairs (C : Family α) (b₂ : ℕ) : Finset (Finset α) :=
  (pairs α).filter (multiplicity C · = b₂)

/-- The last double count in Theorem 6, in additive form. -/
theorem minimum_pairs_bound {C : Family α} {k b₂ : ℕ} (hu : Uniform C k)
    (h₂ : ∀ X : Finset α, X.card = 2 → b₂ ≤ multiplicity C X) :
    (Fintype.card α).choose 2 * (b₂+1) ≤
      k.choose 2 * C.card + (minimumPairs C b₂).card := by
  have hi (X : Finset α) (hX : X ∈ pairs α) :
      b₂+1 ≤ multiplicity C X + if multiplicity C X = b₂ then 1 else 0 := by
    have := h₂ X (mem_pairs.mp hX)
    split_ifs <;> omega
  have hs := sum_le_sum hi
  have hm : (∑ X ∈ pairs α, if multiplicity C X = b₂ then 1 else 0) =
      (minimumPairs C b₂).card := by
    simp only [minimumPairs, card_eq_sum_ones, sum_filter]
  simpa [sum_add_distrib, multiplicity_pair_sum hu, hm, card_pairs, mul_add] using hs

theorem minimum_pairs_card_le {C : Family α} {k b₂ b₃ b₄ : ℕ}
    (hu : Uniform C k) (h₄₃ : b₄ ≤ b₃)
    (h₃ : ∀ X : Finset α, X.card = 3 → b₃ ≤ multiplicity C X)
    (h₄ : ∀ X : Finset α, X.card = 4 → b₄ ≤ multiplicity C X)
    (hd : defect (Fintype.card α) k b₂ b₃ b₄ < diagonal b₂ b₃ b₄) :
    (minimumPairs C b₂).card ≤ C.card := by
  have hS : ∀ X ∈ minimumPairs C b₂, X.card = 2 :=
    fun X hX => mem_pairs.mp (mem_filter.mp hX).1
  apply incidence_rank_obstruction (b₂ := b₂) h₄₃ h₃ h₄ _ hS
  intro X hX
  have hx := hS X hX
  have hm : multiplicity C X = b₂ := (mem_filter.mp hX).2
  have hs : (∑ Y ∈ minimumPairs C b₂, excess C b₃ b₄ X Y) ≤
      ∑ Y ∈ pairs α, excess C b₃ b₄ X Y := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro Y hY _
    exact excess_nonneg h₃ h₄ hx (mem_pairs.mp hY)
  apply hs.trans_lt
  rw [excess_row_sum (b₂ := b₂) hu hx, hm]
  simpa using hd

/-- The structural theorem in terms of subset multiplicities alone. -/
theorem lower_bound_of_multiplicities {C : Family α} {k b₂ b₃ b₄ : ℕ}
    (hu : Uniform C k) (h₄₃ : b₄ ≤ b₃)
    (h₂ : ∀ X : Finset α, X.card = 2 → b₂ ≤ multiplicity C X)
    (h₃ : ∀ X : Finset α, X.card = 3 → b₃ ≤ multiplicity C X)
    (h₄ : ∀ X : Finset α, X.card = 4 → b₄ ≤ multiplicity C X)
    (hd : defect (Fintype.card α) k b₂ b₃ b₄ < diagonal b₂ b₃ b₄) :
    bound (Fintype.card α) k b₂ ≤ C.card := by
  apply (Schoenheim.ceilDiv_le_iff (Nat.succ_pos _)).2
  have hs := minimum_pairs_card_le hu h₄₃ h₃ h₄ hd
  have hc := minimum_pairs_bound hu h₂
  nlinarith

/-- Horsley–Singh Theorem 6, only λ = 1 and s = 2. Every smaller-cover
bound is universally quantified over finite point types and covering families.
All matrix and rank facts are derived, not hypotheses of this theorem. -/
theorem lower_bound {C : Family α} {v k t b₂ b₃ b₄ : ℕ}
    (hp : Parameters v k t b₂ b₃ b₄)
    (h₂ : CoverLower.{u} (v-2) (k-2) (t-2) b₂)
    (h₃ : CoverLower.{u} (v-3) (k-3) (t-3) b₃)
    (h₄ : CoverLower.{u} (v-4) (k-4) (t-4) b₄)
    (hn : Fintype.card α = v) (h : IsCover C k t)
    (hd : defect v k b₂ b₃ b₄ < diagonal b₂ b₃ b₄) :
    bound v k b₂ ≤ C.card := by
  have ht := hp.strength
  rw [← hn] at hd ⊢
  exact lower_bound_of_multiplicities h.1 hp.coefficient_nonneg
    (fun _ hX => multiplicity_ge_of_coverLower hn h (by omega) h₂ hX)
    (fun _ hX => multiplicity_ge_of_coverLower hn h (by omega) h₃ hX)
    (fun _ hX => multiplicity_ge_of_coverLower hn h (by omega) h₄ hX) hd

end CoveringDesigns.HorsleySingh
