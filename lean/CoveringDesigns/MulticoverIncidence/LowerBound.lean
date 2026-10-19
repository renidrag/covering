import CoveringDesigns.MulticoverIncidence.Matrices
import CoveringDesigns.MulticoverIncidence.Parameters

/-! Horsley–Singh Theorem 6 for arbitrary positive λ and admissible s.
The theorem and argument are due to Horsley and Singh.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.MulticoverIncidence
open Finset HigherIncidence
universe u w
variable {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι]

def SmallerBounds (lam v k t s : ℕ) (b : ℕ → ℕ) : Prop :=
  ∀ i, s ≤ i → i ≤ 2*s → Multicover.CoverLower.{u,w} (v-i) (k-i) (t-i) lam (b i)

theorem multiplicity_bounds {B : ι → Finset α} {lam v k t s : ℕ} {b : ℕ → ℕ}
    (ht : 2*s ≤ t) (hb : SmallerBounds.{u,w} lam v k t s b)
    (hn : Fintype.card α=v) (h : Multicover.IsCover B k t lam) :
    ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z := by
  intro Z hlo hhi
  exact Multicover.multiplicity_ge_of_coverLower hn h (by omega) (hb Z.card hlo hhi) rfl

def bound (v k s : ℕ) (b : ℕ → ℕ) : ℕ :=
  Schoenheim.ceilDiv (v.choose s*(b s+1)) (k.choose s+1)

theorem bound_denominator_pos (k s : ℕ) : 0 < k.choose s+1 := Nat.succ_pos _

def minimumSubsets (B : ι → Finset α) (s : ℕ) (b : ℕ → ℕ) : Finset (Finset α) :=
  (subsets α s).filter (indexedSubsetDegree B · = b s)

theorem minimum_subsets_bound {B : ι → Finset α} {k s : ℕ} {b : ℕ → ℕ}
    (hu : Multicover.Uniform B k) (hb : ∀ X : Finset α, X.card=s → b s ≤ indexedSubsetDegree B X) :
    (Fintype.card α).choose s*(b s+1) ≤ k.choose s*Fintype.card ι+(minimumSubsets B s b).card := by
  have hi (X : Finset α) (hx : X ∈ subsets α s) :
      b s+1 ≤ indexedSubsetDegree B X + if indexedSubsetDegree B X=b s then 1 else 0 := by
    have := hb X (mem_subsets.mp hx)
    split_ifs <;> omega
  have hs := sum_le_sum hi
  have hm : (∑ X ∈ subsets α s, if indexedSubsetDegree B X=b s then 1 else 0) =
      (minimumSubsets B s b).card := by
    simp only [minimumSubsets, card_eq_sum_ones, sum_filter]
  simpa [sum_add_distrib, multiplicity_sum hu, hm, mul_add] using hs

theorem minimum_subsets_card_le {B : ι → Finset α} {k s : ℕ} {b : ℕ → ℕ}
    (hu : Multicover.Uniform B k) (ha : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (hd : defect (Fintype.card α) k s b < coefficient s b s) :
    (minimumSubsets B s b).card ≤ Fintype.card ι := by
  have hS : ∀ X ∈ minimumSubsets B s b, X.card=s :=
    fun X hx => mem_subsets.mp (mem_filter.mp hx).1
  apply rank_obstruction ha hb _ hS
  intro X hx
  have hm : indexedSubsetDegree B X=b s := (mem_filter.mp hx).2
  have hs : (∑ Y ∈ minimumSubsets B s b, excess B b X Y) ≤
      ∑ Y ∈ subsets α s, excess B b X Y := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro Y hy _
    exact excess_nonneg hb (hS X hx) (mem_subsets.mp hy)
  apply hs.trans_lt
  rw [excess_row_sum hu b (hS X hx), hm]
  simpa using hd

/-- Division-free Theorem 6 from explicit structural hypotheses. -/
theorem lower_bound_inequality_of_multiplicities {B : ι → Finset α} {k s : ℕ} {b : ℕ → ℕ}
    (hu : Multicover.Uniform B k) (ha : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (hd : defect (Fintype.card α) k s b < coefficient s b s) :
    (Fintype.card α).choose s*(b s+1) ≤ (k.choose s+1)*Fintype.card ι := by
  have hc := minimum_subsets_bound hu (s := s) (b := b)
    (fun X hx => by simpa [hx] using hb X (by omega) (by omega))
  have hr := minimum_subsets_card_le hu ha hb hd
  nlinarith

theorem lower_bound_of_multiplicities {B : ι → Finset α} {k s : ℕ} {b : ℕ → ℕ}
    (hu : Multicover.Uniform B k) (ha : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (hd : defect (Fintype.card α) k s b < coefficient s b s) :
    bound (Fintype.card α) k s b ≤ Fintype.card ι :=
  (Schoenheim.ceilDiv_le_iff (bound_denominator_pos k s)).mpr
    (lower_bound_inequality_of_multiplicities hu ha hb hd)

/-- Theorem 6, with the complete positive-λ numerical and universally quantified
smaller-cover assumptions of Lemma 3, for arbitrary admissible s. -/
theorem lower_bound {B : ι → Finset α} {lam v k t s : ℕ} {b : ℕ → ℕ}
    (hp : Parameters lam v k t s b) (hb : SmallerBounds.{u,w} lam v k t s b)
    (hn : Fintype.card α=v) (h : Multicover.IsCover B k t lam)
    (hd : defect v k s b < coefficient s b s) : bound v k s b ≤ Fintype.card ι := by
  rw [← hn] at hd ⊢
  exact lower_bound_of_multiplicities h.1
    (fun j hj => hp.coefficients j hj.le) (multiplicity_bounds hp.strength hb hn h) hd

/-- Lemma 16 in covering form, with arbitrary s and positive real weights. -/
theorem weighted_covering_obstruction {B : ι → Finset α} {lam v k t s : ℕ} {b : ℕ → ℕ}
    (hp : Parameters lam v k t s b) (hb : SmallerBounds.{u,w} lam v k t s b)
    (hn : Fintype.card α=v) (h : Multicover.IsCover B k t lam)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=s)
    (c : S → ℝ) (hc : ∀ X, 0 < c X)
    (hd : ∀ X : S, ∑ Y : S, (excess B b X.val Y.val : ℝ)*c Y <
      ((coefficient s b s + indexedSubsetDegree B X.val-b s : ℤ) : ℝ)*c X) :
    S.card ≤ Fintype.card ι :=
  weighted_rank_obstruction (fun j hj => hp.coefficients j hj.le)
    (multiplicity_bounds hp.strength hb hn h) S hS c hc hd

/-- The principal division-free statement, with all source hypotheses. -/
theorem lower_bound_inequality {B : ι → Finset α} {lam v k t s : ℕ} {b : ℕ → ℕ}
    (hp : Parameters lam v k t s b) (hb : SmallerBounds.{u,w} lam v k t s b)
    (hn : Fintype.card α=v) (h : Multicover.IsCover B k t lam)
    (hd : defect v k s b < coefficient s b s) :
    v.choose s*(b s+1) ≤ (k.choose s+1)*Fintype.card ι :=
  (Schoenheim.ceilDiv_le_iff (bound_denominator_pos k s)).mp (lower_bound hp hb hn h hd)


end CoveringDesigns.MulticoverIncidence
