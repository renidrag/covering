import CoveringDesigns.AffineConstructions.Geometry
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FinCases

/-! Four residue classes of nonnegative weights on AG(3,2). -/
namespace CoveringDesigns.TwoKMinusTwo
open Finset AffineConstructions
open scoped LinearAlgebra.Projectivization

abbrev Base := Fin 3 → ZMod 2

def tetra : Finset Base := {0, Pi.single 0 1, Pi.single 1 1, Pi.single 2 1}
def pair : Finset Base := {0, Pi.single 0 1}

theorem base_card : Fintype.card Base = 8 := by simp [Base]
theorem tetra_card : tetra.card=4 := by decide
theorem pair_card : pair.card=2 := by decide

theorem tetra_not_in_plane (p : Direction (ZMod 2) 3) (c : ZMod 2) :
    ¬ tetra ⊆ hyperplane p c := by
  classical
  intro h
  have hzero : p.rep (0 : Base) = c := by
    simpa [hyperplane, functionalFiber] using h (show (0 : Base) ∈ tetra by simp [tetra])
  have hc : c=0 := by simpa using hzero.symm
  have hb (i : Fin 3) : p.rep (Pi.single i 1) = 0 := by
    have hm : Pi.single i (1 : ZMod 2) ∈ tetra := by fin_cases i <;> simp [tetra]
    simpa [hyperplane, functionalFiber, hc] using h hm
  apply p.rep_nonzero
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i : Fin 3, x i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply, Function.update, Pi.smul_apply, smul_eq_mul]
  rw [hx, map_sum]
  simp [map_smul, hb]

theorem tetra_plane_card (p : Direction (ZMod 2) 3) (c : ZMod 2) :
    ((hyperplane p c) ∩ tetra).card ≤ 3 := by
  have hle : ((hyperplane p c) ∩ tetra).card ≤ tetra.card := card_le_card inter_subset_right
  by_contra hn
  have he : ((hyperplane p c) ∩ tetra).card = tetra.card := by rw [tetra_card] at *; omega
  have heq : (hyperplane p c) ∩ tetra = tetra := eq_of_subset_of_card_le inter_subset_right he.ge
  exact tetra_not_in_plane p c (by rw [← heq]; exact inter_subset_left)

/-- k=3+4a+j uses the small weights for sizes 3,4,5,6, then adds a everywhere. -/
def weight (a j : ℕ) (x : Base) : ℕ :=
  a + if j=0 then (if x ∈ tetra then 1 else 0)
      else if j=1 then (if x ∈ pair then 0 else 1)
      else if j=2 then 1 else (1 + if x ∈ pair then 1 else 0)

private theorem sum_indicator (S T : Finset Base) :
    (∑ x ∈ S, if x ∈ T then 1 else 0) = (S ∩ T).card := by
  have he : S.filter (· ∈ T) = S ∩ T := by ext x; simp
  rw [← sum_filter, he]
  simp

theorem weight_sum (a j : ℕ) (hj : j<4) :
    (∑ x, weight a j x) = 2*(3+4*a+j)-2 := by
  have hcard : Fintype.card Base=8 := base_card
  have ht := sum_indicator (univ : Finset Base) tetra
  have hp := sum_indicator (univ : Finset Base) pair
  simp only [univ_inter, tetra_card, pair_card] at ht hp
  have hp' : (∑ x : Base, if x ∈ pair then 0 else 1) = 6 := by
    have hh : (∑ x : Base, ((if x ∈ pair then 1 else 0) + (if x ∈ pair then 0 else 1)))=8 := by
      calc
        _ = ∑ _x : Base, 1 := sum_congr rfl (by intro x _; split_ifs <;> omega)
        _ = 8 := by simp [hcard]
    rw [sum_add_distrib, hp] at hh
    omega
  have hcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    simp [weight, sum_add_distrib, hcard, ht, hp, hp'] <;> omega

theorem weight_plane_le (a j : ℕ) (hj : j<4)
    (p : Direction (ZMod 2) 3) (c : ZMod 2) :
    (∑ x ∈ hyperplane p c, weight a j x) ≤ 3+4*a+j := by
  have hcard : (hyperplane p c).card=4 := by simpa using hyperplane_card p c
  have ht := sum_indicator (hyperplane p c) tetra
  have hp := sum_indicator (hyperplane p c) pair
  have htc := tetra_plane_card p c
  have hpc : ((hyperplane p c) ∩ pair).card ≤ 2 := by
    simpa [pair_card] using (card_le_card (inter_subset_right : (hyperplane p c) ∩ pair ⊆ pair))
  have hp' : (∑ x ∈ hyperplane p c, if x ∈ pair then 0 else 1) ≤ 4 := by
    calc
      _ ≤ ∑ _x ∈ hyperplane p c, 1 := sum_le_sum (by intro x _; split_ifs <;> omega)
      _ = 4 := by simp [hcard]
  have hcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    simp only [weight, Nat.reduceEqDiff, ↓reduceIte, sum_add_distrib,
      sum_const, Nat.nsmul_eq_mul, hcard, ht, hp] <;> omega

end CoveringDesigns.TwoKMinusTwo
