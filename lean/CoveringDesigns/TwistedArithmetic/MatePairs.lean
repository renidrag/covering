import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Ring.Nat

/-! Splitting an actual fixed-point-free involution into pairs. -/
namespace CoveringDesigns.TwistedArithmetic
variable {I : Type*} [Fintype I]

noncomputable def MateRepresentatives (f : I → I) :=
  {x : I // Fintype.equivFin I x < Fintype.equivFin I (f x)}

noncomputable instance (f : I → I) : Fintype (MateRepresentatives f) := by
  classical
  unfold MateRepresentatives
  infer_instance

/-- The two copies of the representative type are the two members of each pair. -/
noncomputable def mateEquiv (f : I → I) (hi : Function.Involutive f)
    (hn : ∀ x, f x ≠ x) : (MateRepresentatives f ⊕ MateRepresentatives f) ≃ I := by
  classical
  have back (x : I) (h : ¬ Fintype.equivFin I x < Fintype.equivFin I (f x)) :
      Fintype.equivFin I (f x) < Fintype.equivFin I (f (f x)) := by
    rw [hi x]
    exact lt_of_le_of_ne (le_of_not_gt h) (fun he => hn x ((Fintype.equivFin I).injective he))
  refine {
    toFun := fun z => Sum.elim Subtype.val (fun y => f y.val) z
    invFun := fun x => if h : Fintype.equivFin I x < Fintype.equivFin I (f x)
      then Sum.inl ⟨x,h⟩ else Sum.inr ⟨f x,back x h⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    rcases z with x|x
    · dsimp only [Sum.elim]
      rw [dif_pos x.property]
      rfl
    · have h : ¬ Fintype.equivFin I (f x.val) < Fintype.equivFin I (f (f x.val)) := by
        rw [hi x.val]
        exact not_lt_of_gt x.property
      dsimp only [Sum.elim]
      rw [dif_neg h]
      congr 1
      exact Subtype.ext (hi x.val)
  · intro x
    dsimp only
    split_ifs
    · rfl
    · exact hi x

theorem mateEquiv_swap (f : I → I) (hi : Function.Involutive f) (hn : ∀ x, f x ≠ x)
    (z : MateRepresentatives f ⊕ MateRepresentatives f) :
    mateEquiv f hi hn z.swap = f (mateEquiv f hi hn z) := by
  cases z with
  | inl x => rfl
  | inr x => exact (hi x.val).symm

theorem mateRepresentatives_card (f : I → I) (hi : Function.Involutive f)
    (hn : ∀ x, f x ≠ x) : 2 * Fintype.card (MateRepresentatives f) = Fintype.card I := by
  have h := Fintype.card_congr (mateEquiv f hi hn)
  simpa [two_mul] using h

end CoveringDesigns.TwistedArithmetic
