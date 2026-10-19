import CoveringDesigns.MulticoverLargeDefect.LowerBound
import CoveringDesigns.MulticoverIncidence.Family
import CoveringDesigns.LargeDefect.LowerBound

/-! Multiplicity-one compatibility, including universal smaller-cover bounds.
The old Family-specific theorem is not used to prove the indexed theorem.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.MulticoverLargeDefect
open Finset HigherIncidence
universe u

/-- Both full hypothesis packages agree at multiplicity one. -/
theorem family_hypotheses_iff {v k t s : ℕ} {b : ℕ → ℕ} :
    (MulticoverIncidence.Parameters 1 v k t s b ∧
      MulticoverIncidence.SmallerBounds.{u,u} 1 v k t s b) ↔
    (HigherIncidence.Parameters v k t s b ∧ HigherIncidence.SmallerBounds.{u} v k t s b) :=
  and_congr MulticoverIncidence.parameters_one_iff MulticoverIncidence.smallerBounds_one_iff

theorem value_eq_ordinary (v k s : ℕ) (b : ℕ → ℕ) :
    value v k s b = LargeDefect.value v k s b := rfl

theorem bound_eq_ordinary (v k s : ℕ) (b : ℕ → ℕ) :
    bound v k s b = LargeDefect.bound v k s b := rfl

/-- The established ordinary Theorem 15 contract follows from the indexed theorem,
using deduplication only in the multiplicity-one universal-bound adapter. -/
theorem family_lower_bound {α : Type u} [Fintype α] [DecidableEq α]
    {C : Family α} {v k t s : ℕ} {b : ℕ → ℕ}
    (hp : HigherIncidence.Parameters v k t s b)
    (hb : HigherIncidence.SmallerBounds.{u} v k t s b)
    (hn : Fintype.card α=v) (h : CoveringDesigns.IsCover C k t)
    (hmK : b s < k.choose s) (ha : 1 ≤ coefficient s b s)
    (had : coefficient s b s ≤ defect v k s b) : LargeDefect.bound v k s b ≤ C.card := by
  simpa only [bound_eq_ordinary, Multicover.ofFamily_card] using
    lower_bound (MulticoverIncidence.parameters_one_iff.mpr hp)
      (MulticoverIncidence.smallerBounds_of_family hb) hn
      ((Multicover.ofFamily_isCover_one C k t).mpr h) hmK ha had

end CoveringDesigns.MulticoverLargeDefect
