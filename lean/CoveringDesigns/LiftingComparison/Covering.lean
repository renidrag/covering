import CoveringDesigns.LiftingComparison.Iteration

/-! An explicit universal residual seed lifts through occurrence-preserving links.
The numerical seed need not be the covering multiplicity. -/
namespace CoveringDesigns.LiftingComparison
universe u w

/-- All natural multiplicities are supported, including zero. Repeated blocks
remain separately indexed. The residual seed is a separate universal theorem. -/
theorem lift_coverLower {v k t s lam h : ℕ}
    (hst : s ≤ t) (htk : t ≤ k) (hkv : k ≤ v)
    (hs : Multicover.CoverLower.{u,w} (v-s) (k-s) (t-s) lam h) :
    Multicover.CoverLower.{u,w} v k t lam (iterate v k s h) := by
  induction s generalizing v k t with
  | zero =>
    simp only [Nat.sub_zero] at hs
    exact hs
  | succ s ih =>
    cases v with
    | zero => omega
    | succ v =>
      cases k with
      | zero => omega
      | succ k =>
        cases t with
        | zero => omega
        | succ t =>
          simp only [Nat.succ_sub_succ_eq_sub] at hs
          have hl : Multicover.CoverLower.{u,w} v k t lam (iterate v k s h) :=
            ih (by omega) (by omega) (by omega) hs
          intro α ι _ _ _ B hn hc
          simpa only [iterate_succ, Nat.add_sub_cancel] using
            Multicover.lift_lower_bound hn hc hl

theorem indexed_lower_bound {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι]
    {B : ι → Finset α} {v k t s lam h : ℕ}
    (hst : s ≤ t) (htk : t ≤ k) (hkv : k ≤ v)
    (hs : Multicover.CoverLower.{u,w} (v-s) (k-s) (t-s) lam h)
    (hn : Fintype.card α = v) (hc : Multicover.IsCover B k t lam) :
    iterate v k s h ≤ Fintype.card ι :=
  lift_coverLower hst htk hkv hs hn hc

/-- The comparison and the covering conclusion have independent premises.
In particular the stronger seed m+1 is not inferred from a bound m. -/
theorem indexed_comparison_bound {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι]
    {B : ι → Finset α} {v k t s lam m : ℕ} {A D : ℝ}
    (hst : s ≤ t) (htk : t ≤ k) (hkv : k ≤ v)
    (hs : Multicover.CoverLower.{u,w} (v-s) (k-s) (t-s) lam (m+1))
    (hn : Fintype.card α = v) (hc : Multicover.IsCover B k t lam)
    (hden : 0 < (k.choose s : ℝ)*(A-D)+1)
    (hthreshold : (k.choose s : ℝ)*D ≤ m+1) :
    ⌈LargeDefect.ratio (v.choose s) (k.choose s) m A D⌉₊ ≤ iterate v k s (m+1) ∧
      iterate v k s (m+1) ≤ Fintype.card ι :=
  ⟨remark14 (hst.trans htk) hkv hden hthreshold,
    indexed_lower_bound hst htk hkv hs hn hc⟩

end CoveringDesigns.LiftingComparison
