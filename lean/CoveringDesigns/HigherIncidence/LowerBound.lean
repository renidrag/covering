import CoveringDesigns.HigherIncidence.Matrices
import CoveringDesigns.HigherIncidence.Parameters
import CoveringDesigns.Weighted.Counting

/-! Horsley–Singh Theorem 6 for λ=1 and every admissible s.
The theorem and original argument are due to Horsley and Singh.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.HigherIncidence
open Finset HorsleySingh
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

def SmallerBounds (v k t s : ℕ) (b : ℕ → ℕ) : Prop :=
  ∀ i, s ≤ i → i ≤ 2*s → CoverLower.{u} (v-i) (k-i) (t-i) (b i)

theorem multiplicity_bounds {C : Family α} {v k t s : ℕ} {b : ℕ → ℕ}
    (ht : 2*s ≤ t) (hb : SmallerBounds.{u} v k t s b)
    (hn : Fintype.card α=v) (h : IsCover C k t) :
    ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ multiplicity C Z := by
  intro Z hlo hhi
  exact multiplicity_ge_of_coverLower hn h (by omega) (hb Z.card hlo hhi) rfl

def bound (v k s : ℕ) (b : ℕ → ℕ) : ℕ :=
  Schoenheim.ceilDiv (v.choose s*(b s+1)) (k.choose s+1)

theorem bound_denominator_pos (k s : ℕ) : 0 < k.choose s+1 := Nat.succ_pos _

def minimumSubsets (C : Family α) (s : ℕ) (b : ℕ → ℕ) : Finset (Finset α) :=
  (subsets α s).filter (multiplicity C · = b s)

theorem minimum_subsets_bound {C : Family α} {k s : ℕ} {b : ℕ → ℕ}
    (hu : Uniform C k) (hb : ∀ X : Finset α, X.card=s → b s ≤ multiplicity C X) :
    (Fintype.card α).choose s*(b s+1) ≤ k.choose s*C.card+(minimumSubsets C s b).card := by
  have hi (X : Finset α) (hx : X ∈ subsets α s) :
      b s+1 ≤ multiplicity C X + if multiplicity C X=b s then 1 else 0 := by
    have := hb X (mem_subsets.mp hx)
    split_ifs <;> omega
  have hs := sum_le_sum hi
  have hm : (∑ X ∈ subsets α s, if multiplicity C X=b s then 1 else 0) =
      (minimumSubsets C s b).card := by
    simp only [minimumSubsets, card_eq_sum_ones, sum_filter]
  simpa [sum_add_distrib, multiplicity_sum hu, hm, mul_add] using hs

theorem minimum_subsets_card_le {C : Family α} {k s : ℕ} {b : ℕ → ℕ}
    (hu : Uniform C k) (ha : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ multiplicity C Z)
    (hd : defect (Fintype.card α) k s b < coefficient s b s) :
    (minimumSubsets C s b).card ≤ C.card := by
  have hS : ∀ X ∈ minimumSubsets C s b, X.card=s :=
    fun X hx => mem_subsets.mp (mem_filter.mp hx).1
  apply rank_obstruction ha hb _ hS
  intro X hx
  have hm : multiplicity C X=b s := (mem_filter.mp hx).2
  have hs : (∑ Y ∈ minimumSubsets C s b, excess C b X Y) ≤
      ∑ Y ∈ subsets α s, excess C b X Y := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro Y hy _
    exact excess_nonneg hb (hS X hx) (mem_subsets.mp hy)
  apply hs.trans_lt
  rw [excess_row_sum hu b (hS X hx), hm]
  simpa using hd

/-- The structural bound from uniformity and multiplicity inequalities. -/
theorem lower_bound_of_multiplicities {C : Family α} {k s : ℕ} {b : ℕ → ℕ}
    (hu : Uniform C k) (ha : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ multiplicity C Z)
    (hd : defect (Fintype.card α) k s b < coefficient s b s) :
    bound (Fintype.card α) k s b ≤ C.card := by
  apply (Schoenheim.ceilDiv_le_iff (bound_denominator_pos k s)).mpr
  have hc := minimum_subsets_bound hu (s := s) (b := b)
    (fun X hx => by simpa [hx] using hb X (by omega) (by omega))
  have hr := minimum_subsets_card_le hu ha hb hd
  nlinarith

/-- Theorem 6, with exactly the λ=1 numerical and universally quantified
smaller-cover assumptions of Lemma 3, for arbitrary admissible s. -/
theorem lower_bound {C : Family α} {v k t s : ℕ} {b : ℕ → ℕ}
    (hp : Parameters v k t s b) (hb : SmallerBounds.{u} v k t s b)
    (hn : Fintype.card α=v) (h : IsCover C k t)
    (hd : defect v k s b < coefficient s b s) : bound v k s b ≤ C.card := by
  rw [← hn] at hd ⊢
  exact lower_bound_of_multiplicities h.1
    (fun j hj => hp.coefficients j hj.le) (multiplicity_bounds hp.strength hb hn h) hd

/-- Lemma 16 in covering form, with arbitrary s and positive real weights. -/
theorem weighted_covering_obstruction {C : Family α} {v k t s : ℕ} {b : ℕ → ℕ}
    (hp : Parameters v k t s b) (hb : SmallerBounds.{u} v k t s b)
    (hn : Fintype.card α=v) (h : IsCover C k t)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=s)
    (c : S → ℝ) (hc : ∀ X, 0 < c X)
    (hd : ∀ X : S, ∑ Y : S, (excess C b X.val Y.val : ℝ)*c Y <
      ((coefficient s b s + multiplicity C X.val-b s : ℤ) : ℝ)*c X) :
    S.card ≤ C.card :=
  weighted_rank_obstruction (fun j hj => hp.coefficients j hj.le)
    (multiplicity_bounds hp.strength hb hn h) S hS c hc hd

/-- Covering-specific instance of the already proved weighted accounting.
The selection inequality remains explicit; no selection theorem is assumed. -/
theorem two_level_bound {C : Family α} {k s m : ℕ} {a β : ℝ}
    (hu : Uniform C k) (hβ : 0 ≤ β) (ha : 2*β ≤ a)
    (hb : ∀ X : Finset α, X.card=s → m ≤ multiplicity C X)
    (hr : a*((subsets α s).filter (multiplicity C · = m)).card +
      β*((subsets α s).filter (multiplicity C · = m+1)).card ≤ C.card) :
    ((Fintype.card α).choose s : ℝ)*((m : ℝ)*(a-β)+a) ≤
      (C.card : ℝ)*((k.choose s : ℝ)*(a-β)+1) := by
  simpa only [card_subsets] using Weighted.two_level_bound (subsets α s) (multiplicity C)
    hβ ha (fun X hx => hb X (mem_subsets.mp hx)) (multiplicity_sum hu s) hr

theorem two_level_ceiling {C : Family α} {k s m : ℕ} {a β : ℝ}
    (hu : Uniform C k) (hβ : 0 ≤ β) (ha : 2*β ≤ a)
    (hb : ∀ X : Finset α, X.card=s → m ≤ multiplicity C X)
    (hr : a*((subsets α s).filter (multiplicity C · = m)).card +
      β*((subsets α s).filter (multiplicity C · = m+1)).card ≤ C.card) :
    ⌈((Fintype.card α).choose s : ℝ)*((m : ℝ)*(a-β)+a) /
      ((k.choose s : ℝ)*(a-β)+1)⌉₊ ≤ C.card := by
  simpa only [card_subsets] using Weighted.two_level_ceiling (subsets α s) (multiplicity C)
    hβ ha (fun X hx => hb X (mem_subsets.mp hx)) (multiplicity_sum hu s) hr

end CoveringDesigns.HigherIncidence
