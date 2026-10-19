import CoveringDesigns.Weighted.Matrix
import CoveringDesigns.HorsleySingh.Matrices

/-! Selected-pair integration of the general weighted rank criterion.
This is the pair specialisation of Horsley–Singh Lemma 16, not an arbitrary-s
covering theorem. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.Weighted
open Finset Matrix HorsleySingh
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Weighted strict dominance on any selected pair set bounds its size by
the number of blocks. No uniformity, coverage or nonemptiness is assumed. -/
theorem selected_pairs_card_le {C : Family α} {b₂ b₃ b₄ : ℕ}
    (h₄₃ : b₄ ≤ b₃)
    (h₃ : ∀ X : Finset α, X.card = 3 → b₃ ≤ multiplicity C X)
    (h₄ : ∀ X : Finset α, X.card = 4 → b₄ ≤ multiplicity C X)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card = 2)
    (c : S → ℝ) (hc : ∀ X, 0 < c X)
    (hd : ∀ X : S, ∑ Y : S, (excess C b₃ b₄ X.val Y.val : ℝ) * c Y <
      ((diagonal b₂ b₃ b₄ + multiplicity C X.val - b₂ : ℤ) : ℝ) * c X) :
    S.card ≤ C.card := by
  have hs (X Y : S) : excessMatrix C b₃ b₄ S X Y = excessMatrix C b₃ b₄ S Y X :=
    congrArg Int.cast (excess_comm C b₃ b₄ X.val Y.val)
  have hn (X Y : S) : 0 ≤ excessMatrix C b₃ b₄ S X Y := by
    change (0 : ℝ) ≤ (excess C b₃ b₄ X.val Y.val : ℝ)
    exact_mod_cast excess_nonneg h₃ h₄ (hS X.val X.property) (hS Y.val Y.property)
  simpa only [Fintype.card_coe] using gram_card_le_of_weighted_row_sum_lt
    (incidence C S)
    (fun X : S => ((diagonal b₂ b₃ b₄ + multiplicity C X.val - b₂ : ℤ) : ℝ))
    c (excessMatrix C b₃ b₄ S) (positivePart b₃ b₄ S)
    hs hn hc hd (positivePart_posSemidef h₄₃ S) (incidence_gram_eq C b₂ b₃ b₄ S hS)

end CoveringDesigns.Weighted
