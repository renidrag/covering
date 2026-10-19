import CoveringDesigns.MulticoverIncidence.Counting
import CoveringDesigns.Weighted.Counting

/-! Indexed incidence instances of the existing general weighted accounting.
No graph, rank, or covering assumption is built into these interfaces.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.MulticoverLargeDefect
open Finset HigherIncidence MulticoverIncidence
universe u w
variable {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι]

theorem incidence_bound {B : ι → Finset α} {k s m : ℕ}
    (hu : Multicover.Uniform B k)
    (hb : ∀ X : Finset α, X.card=s → m ≤ indexedSubsetDegree B X) :
    (Fintype.card α).choose s*m ≤ k.choose s*Fintype.card ι := by
  have hh := sum_le_sum (s := subsets α s) (fun X hx => hb X (mem_subsets.mp hx))
  simpa [sum_const, nsmul_eq_mul, card_subsets, multiplicity_sum hu] using hh

theorem two_level_bound {B : ι → Finset α} {k s m : ℕ} {A D : ℝ}
    (hu : Multicover.Uniform B k) (hD : 0 ≤ D) (hAD : 2*D ≤ A)
    (hb : ∀ X : Finset α, X.card=s → m ≤ indexedSubsetDegree B X)
    (hr : A*((subsets α s).filter (indexedSubsetDegree B · = m)).card +
      D*((subsets α s).filter (indexedSubsetDegree B · = m+1)).card ≤ Fintype.card ι) :
    ((Fintype.card α).choose s : ℝ)*((m : ℝ)*(A-D)+A) ≤
      (Fintype.card ι : ℝ)*((k.choose s : ℝ)*(A-D)+1) := by
  simpa only [card_subsets] using Weighted.two_level_bound (subsets α s)
    (indexedSubsetDegree B) hD hAD (fun X hx => hb X (mem_subsets.mp hx))
    (multiplicity_sum hu s) hr

theorem two_level_ceiling {B : ι → Finset α} {k s m : ℕ} {A D : ℝ}
    (hu : Multicover.Uniform B k) (hD : 0 ≤ D) (hAD : 2*D ≤ A)
    (hb : ∀ X : Finset α, X.card=s → m ≤ indexedSubsetDegree B X)
    (hr : A*((subsets α s).filter (indexedSubsetDegree B · = m)).card +
      D*((subsets α s).filter (indexedSubsetDegree B · = m+1)).card ≤ Fintype.card ι) :
    ⌈((Fintype.card α).choose s : ℝ)*((m : ℝ)*(A-D)+A) /
      ((k.choose s : ℝ)*(A-D)+1)⌉₊ ≤ Fintype.card ι :=
  Nat.ceil_le.mpr ((div_le_iff₀ (Weighted.two_level_denominator_pos _ hD hAD)).mpr
    (two_level_bound hu hD hAD hb hr))

end CoveringDesigns.MulticoverLargeDefect
