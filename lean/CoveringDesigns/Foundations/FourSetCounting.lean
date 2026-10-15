import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
The counting obstruction for four finite sets with the 8/4/2 intersection
profile. These are generic kernel proofs. This module does not assert that
any star catalogue satisfies the profile; that is a separate obligation.
-/

namespace CoveringDesigns

open Finset

variable {α : Type*} [DecidableEq α]

/-- Three-set inclusion-exclusion, written without natural-number subtraction. -/
theorem card_union_three_balance (A B C : Finset α) :
    (A ∪ B ∪ C).card + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card =
      A.card + B.card + C.card + (A ∩ B ∩ C).card := by
  have hAB := card_union_add_card_inter A B
  have hABC := card_union_add_card_inter (A ∪ B) C
  have hACBC := card_union_add_card_inter (A ∩ C) (B ∩ C)
  have hi : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x
    simp [and_left_comm]
  rw [union_inter_distrib_right] at hABC
  rw [hi] at hACBC
  omega

/-- Four-set inclusion-exclusion, written as an equality of nonnegative sums. -/
theorem card_union_four_balance (A B C D : Finset α) :
    (A ∪ B ∪ C ∪ D).card +
        (A ∩ B).card + (A ∩ C).card + (A ∩ D).card +
        (B ∩ C).card + (B ∩ D).card + (C ∩ D).card +
        (A ∩ B ∩ C ∩ D).card =
      A.card + B.card + C.card + D.card +
        (A ∩ B ∩ C).card + (A ∩ B ∩ D).card +
        (A ∩ C ∩ D).card + (B ∩ C ∩ D).card := by
  have hABC := card_union_three_balance A B C
  have hABCD := card_union_add_card_inter (A ∪ B ∪ C) D
  have hD := card_union_three_balance (A ∩ D) (B ∩ D) (C ∩ D)
  have hAB : (A ∩ D) ∩ (B ∩ D) = A ∩ B ∩ D := by
    ext x
    simp [and_left_comm]
  have hAC : (A ∩ D) ∩ (C ∩ D) = A ∩ C ∩ D := by
    ext x
    simp [and_left_comm]
  have hBC : (B ∩ D) ∩ (C ∩ D) = B ∩ C ∩ D := by
    ext x
    simp [and_left_comm]
  have hABCD' : (A ∩ B ∩ D) ∩ (C ∩ D) = A ∩ B ∩ C ∩ D := by
    ext x
    simp [and_left_comm]
  rw [union_inter_distrib_right, union_inter_distrib_right] at hABCD
  rw [hAB, hAC, hBC, hABCD'] at hD
  omega

/-- For the 8/4/2 profile, the union and fourfold intersection total sixteen. -/
theorem four_star_count_identity (A B C D : Finset α)
    (hsingle : A.card = 8 ∧ B.card = 8 ∧ C.card = 8 ∧ D.card = 8)
    (hpair : (A ∩ B).card = 4 ∧ (A ∩ C).card = 4 ∧ (A ∩ D).card = 4 ∧
      (B ∩ C).card = 4 ∧ (B ∩ D).card = 4 ∧ (C ∩ D).card = 4)
    (htriple : (A ∩ B ∩ C).card = 2 ∧ (A ∩ B ∩ D).card = 2 ∧
      (A ∩ C ∩ D).card = 2 ∧ (B ∩ C ∩ D).card = 2) :
    (A ∪ B ∪ C ∪ D).card + (A ∩ B ∩ C ∩ D).card = 16 := by
  have h := card_union_four_balance A B C D
  omega

/-- Four stars with the 8/4/2 profile and at most one common block need at
least fifteen distinct blocks, so cannot fit in a fourteen-block remainder. -/
theorem four_star_union_at_least_fifteen (A B C D : Finset α)
    (hsingle : A.card = 8 ∧ B.card = 8 ∧ C.card = 8 ∧ D.card = 8)
    (hpair : (A ∩ B).card = 4 ∧ (A ∩ C).card = 4 ∧ (A ∩ D).card = 4 ∧
      (B ∩ C).card = 4 ∧ (B ∩ D).card = 4 ∧ (C ∩ D).card = 4)
    (htriple : (A ∩ B ∩ C).card = 2 ∧ (A ∩ B ∩ D).card = 2 ∧
      (A ∩ C ∩ D).card = 2 ∧ (B ∩ C ∩ D).card = 2)
    (hfour : (A ∩ B ∩ C ∩ D).card ≤ 1) :
    15 ≤ (A ∪ B ∪ C ∪ D).card := by
  have h := four_star_count_identity A B C D hsingle hpair htriple
  omega

#print axioms card_union_four_balance
#print axioms four_star_union_at_least_fifteen

end CoveringDesigns
