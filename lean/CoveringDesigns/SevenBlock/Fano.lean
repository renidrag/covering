import CoveringDesigns.Foundations.Basic
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The explicit seven-position Fano incidence table, independent of Stanton.
Finite kernel reductions check this fixed table, not families of coverings. -/
namespace CoveringDesigns.SevenBlock
open Finset

/-- Binary xor lines, after shifting the labels 1,…,7 down by one. -/
def line : Fin 7 → Finset (Fin 7) :=
  ![{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}]

def highSupport (tag h : Bool) : Finset (Fin 7) :=
  if tag ∨ h then {2,4,5,6} else {1,3,5,6}

section FixedIncidence
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem line_card : ∀ l, (line l).card = 3 := by decide +kernel

theorem line_meet : ∀ l m, (line l ∩ line m).Nonempty := by decide +kernel

theorem line_inter_card : ∀ l m, l ≠ m → (line l ∩ line m).card = 1 := by decide +kernel

theorem line_injective : Function.Injective line := by
  unfold Function.Injective
  decide +kernel

theorem pair_unique_line : ∀ i j : Fin 7, i ≠ j → ∃! l, i ∈ line l ∧ j ∈ line l := by
  unfold ExistsUnique
  decide +kernel

theorem position_degree : ∀ i : Fin 7, (univ.filter fun l => i ∈ line l).card = 3 := by
  decide +kernel

theorem high_card : ∀ tag h, (highSupport tag h).card = 4 := by decide +kernel

theorem high_line_meet : ∀ tag h l, (highSupport tag h ∩ line l).Nonempty := by
  decide +kernel

theorem high_high_meet : ∀ tag h g, (highSupport tag h ∩ highSupport tag g).Nonempty := by
  decide +kernel

theorem exceptional_codegree : ∀ tag,
    (highSupport tag false ∩ highSupport tag true).card = if tag then 4 else 2 := by
  decide +kernel

end FixedIncidence

/-- The Fano incidence inverse over integers, without division or a rank
premise. Line self-intersection is three and every other intersection one. -/
theorem fano_incidence_identity (W : Fin 7 → ℤ) (l : Fin 7) :
    2 * W l + ∑ m, W m =
      ∑ i ∈ line l, ∑ m : Fin 7, if i ∈ line m then W m else 0 := by
  fin_cases l <;> simp [line, Fin.sum_univ_succ] <;> ring

/-- Row sums determine every line weight. -/
theorem fano_weights_unique (W U : Fin 7 → ℤ)
    (h : ∀ i, (∑ l : Fin 7, if i ∈ line l then W l else 0) =
      ∑ l : Fin 7, if i ∈ line l then U l else 0) : W = U := by
  have ht : ∑ l, W l = ∑ l, U l := by
    have hs := congrArg (fun f : Fin 7 → ℤ => ∑ i, f i) (funext h)
    simp [line, Fin.sum_univ_succ] at hs ⊢
    omega
  funext l
  have hW := fano_incidence_identity W l
  have hU := fano_incidence_identity U l
  simp_rw [h] at hW
  omega

#guard_standard_axioms line_card line_meet line_inter_card line_injective
  pair_unique_line position_degree high_card high_line_meet high_high_meet
  exceptional_codegree fano_incidence_identity fano_weights_unique

end CoveringDesigns.SevenBlock
