import CoveringDesigns.MulticoverLargeDefect.LowerBound

/-! Three fixed arbitrary-multiplicity calibrations and structural boundaries.
No improved bound, exact value, construction or priority is claimed.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.MulticoverLargeDefect.Examples
open Finset HigherIncidence MulticoverIncidence LargeDefect
universe u w

def seeds5 (i : ℕ) : ℕ := Multicover.bound 2 (5-i) (4-i) (2-i)

theorem seeds5_values : seeds5 1=3 ∧ seeds5 2=2 := by decide

theorem parameters5 : MulticoverIncidence.Parameters 2 5 4 2 1 seeds5 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide, ?_, ?_⟩
  · intro i hlo hhi
    interval_cases i <;> decide
  · intro i hlo hhi
    interval_cases i; decide
  · intro j hj
    interval_cases j <;> decide

theorem smaller_bounds5 : MulticoverIncidence.SmallerBounds.{u,w} 2 5 4 2 1 seeds5 := by
  intro i hlo hhi
  exact Multicover.schoenheim_coverLower (by omega) (by omega)

theorem data5 : coefficient 1 seeds5 1=1 ∧ defect 5 4 1 seeds5=1 ∧
    (5 : ℕ).choose 1=5 ∧ (4 : ℕ).choose 1=4 ∧
    Multicover.bound 2 5 4 2=4 := by decide

theorem value5 : MulticoverLargeDefect.value 5 4 1 seeds5=35/11 := by
  norm_num [MulticoverLargeDefect.value, ratio, alpha, beta, data5.1, data5.2.1,
    data5.2.2.1, data5.2.2.2.1, seeds5_values.1]

theorem bound5 : MulticoverLargeDefect.bound 5 4 1 seeds5=4 := by
  rw [MulticoverLargeDefect.bound, value5]
  apply (Nat.ceil_eq_iff (by norm_num)).mpr
  norm_num

theorem covering5 {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    (hn : Fintype.card α=5) (h : Multicover.IsCover B 4 2 2) : 4 ≤ Fintype.card ι := by
  rw [← bound5]
  exact MulticoverLargeDefect.lower_bound parameters5 smaller_bounds5 hn h
    (by decide) (by decide) (by decide)

def seeds10 (i : ℕ) : ℕ := Multicover.bound 2 (10-i) (6-i) (4-i)

theorem seeds10_values : seeds10 2=10 ∧ seeds10 3=5 ∧ seeds10 4=2 := by decide

theorem parameters10 : MulticoverIncidence.Parameters 2 10 6 4 2 seeds10 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide, ?_, ?_⟩
  · intro i hlo hhi
    interval_cases i <;> decide
  · intro i hlo hhi
    interval_cases i <;> decide
  · intro j hj
    interval_cases j <;> decide

theorem smaller_bounds10 : MulticoverIncidence.SmallerBounds.{u,w} 2 10 6 4 2 seeds10 := by
  intro i hlo hhi
  exact Multicover.schoenheim_coverLower (by omega) (by omega)

theorem data10 : coefficient 2 seeds10 2=2 ∧ defect 10 6 2 seeds10=4 ∧
    (10 : ℕ).choose 2=45 ∧ (6 : ℕ).choose 2=15 ∧
    Multicover.bound 2 10 6 4=30 := by decide

theorem value10 : MulticoverLargeDefect.value 10 6 2 seeds10=4293/164 := by
  norm_num [MulticoverLargeDefect.value, ratio, alpha, beta, data10.1, data10.2.1,
    data10.2.2.1, data10.2.2.2.1, seeds10_values.1]

theorem bound10 : MulticoverLargeDefect.bound 10 6 2 seeds10=27 := by
  rw [MulticoverLargeDefect.bound, value10]
  apply (Nat.ceil_eq_iff (by norm_num)).mpr
  norm_num

theorem covering10 {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    (hn : Fintype.card α=10) (h : Multicover.IsCover B 6 4 2) : 27 ≤ Fintype.card ι := by
  rw [← bound10]
  exact MulticoverLargeDefect.lower_bound parameters10 smaller_bounds10 hn h
    (by decide) (by decide) (by decide)

def seeds11 (i : ℕ) : ℕ := Multicover.bound 2 (11-i) (6-i) (4-i)

theorem seeds11_values : seeds11 2=14 ∧ seeds11 3=6 ∧ seeds11 4=2 := by decide

theorem parameters11 : MulticoverIncidence.Parameters 2 11 6 4 2 seeds11 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide, ?_, ?_⟩
  · intro i hlo hhi
    interval_cases i <;> decide
  · intro i hlo hhi
    interval_cases i <;> decide
  · intro j hj
    interval_cases j <;> decide

theorem smaller_bounds11 : MulticoverIncidence.SmallerBounds.{u,w} 2 11 6 4 2 seeds11 := by
  intro i hlo hhi
  exact Multicover.schoenheim_coverLower (by omega) (by omega)

theorem data11 : coefficient 2 seeds11 2=4 ∧ defect 11 6 2 seeds11=16 ∧
    (11 : ℕ).choose 2=55 ∧ (6 : ℕ).choose 2=15 ∧
    Multicover.bound 2 11 6 4=52 := by decide

theorem value11 : MulticoverLargeDefect.value 11 6 2 seeds11=62425/2104 := by
  norm_num [MulticoverLargeDefect.value, ratio, alpha, beta, data11.1, data11.2.1,
    data11.2.2.1, data11.2.2.2.1, seeds11_values.1]

theorem bound11 : MulticoverLargeDefect.bound 11 6 2 seeds11=30 := by
  rw [MulticoverLargeDefect.bound, value11]
  apply (Nat.ceil_eq_iff (by norm_num)).mpr
  norm_num

theorem covering11 {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    (hn : Fintype.card α=11) (h : Multicover.IsCover B 6 4 2) : 30 ≤ Fintype.card ι := by
  rw [← bound11]
  exact MulticoverLargeDefect.lower_bound parameters11 smaller_bounds11 hn h
    (by decide) (by decide) (by decide)

/-- Both exact integer branches are exercised by the pair calibrations. -/
theorem counting_branches :
    defect 10 6 2 seeds10+2 ≤ ((6 : ℕ).choose 2 : ℤ) ∧
    ((6 : ℕ).choose 2 : ℤ) ≤ defect 11 6 2 seeds11+1 := by decide

/-- The exact coefficient boundary, using the existing cross-multiplication algebra. -/
theorem coefficient_boundary {K : ℕ} {a d : ℝ} (hK : 0 < K)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (he : d+2=(K : ℝ)) :
    2*beta K a d=alpha a d := by
  have hle := (coefficient_two_level_iff hK ha hd).mpr he.le
  have hn : d+1 ≠ 0 := by linarith
  unfold alpha beta at *
  rw [← he] at *
  field_simp
  ring

/-- The adjacent integer fallback is outside the weighted-counting coefficient range. -/
theorem adjacent_fallback {K : ℕ} {a d : ℝ} (hK : 0 < K)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (he : d+1=(K : ℝ)) :
    alpha a d < 2*beta K a d ∧ alpha a d*K=(a+1)/2 := by
  constructor
  · apply lt_of_not_ge
    rw [coefficient_two_level_iff hK ha hd]
    linarith
  · unfold alpha
    rw [← he]
    have hh : d+1 ≠ 0 := by linarith
    field_simp [hh]

/-- Rank remains available for the empty selection, without a chosen row. -/
theorem empty_selection {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    {b : ℕ → ℕ} {s a : ℕ} (hac : (a : ℤ) ≤ coefficient s b s)
    (hc : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z) :
    (∅ : Finset (Finset α)).card ≤ Fintype.card ι :=
  independent_card_le hac hc hb ∅ (by simp) (by simp)

/-- Empty low classes contribute zero; the full selection argument still applies. -/
theorem empty_low_classes {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    {b : ℕ → ℕ} {k s : ℕ} (hu : Multicover.Uniform B k) (hK : 0 < k.choose s)
    (hc : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (ha : 1 ≤ coefficient s b s)
    (had : coefficient s b s ≤ defect (Fintype.card α) k s b)
    (h0 : ((subsets α s).filter (indexedSubsetDegree B · = b s))=∅)
    (h1 : ((subsets α s).filter (indexedSubsetDegree B · = b s+1))=∅) :
    (0 : ℝ) ≤ Fintype.card ι := by
  simpa only [h0, h1, card_empty, Nat.cast_zero, mul_zero, zero_add] using
    selection_bound hu hK hc hb ha had

/-- The deepest links retain their occurrence multiplicity at residual strength zero. -/
theorem boundary_link {α : Type u} {ι : Type w} [DecidableEq α] [Fintype ι]
    {B : ι → Finset α} {k s lam : ℕ} (h : Multicover.IsCover B k (2*s) lam)
    {X : Finset α} (hx : X.card=2*s) :
    Multicover.IsCover (Multicover.subsetLink B X) (k-2*s) 0 lam ∧
      lam ≤ Fintype.card {i // X ⊆ B i} := by
  have hl : Multicover.IsCover (Multicover.subsetLink B X) (k-2*s) 0 lam := by
    simpa only [hx, Nat.sub_self] using Multicover.subsetLink_isCover h X (by omega)
  exact ⟨hl, (Multicover.covers_zero_iff (Multicover.subsetLink B X) lam).mp hl.2⟩

def repeatedBlocks (_i : Fin 3) : Finset (Fin 2) := univ

theorem repeated_columns : repeatedBlocks 0 = repeatedBlocks 1 := rfl

theorem repeated_cover : Multicover.IsCover repeatedBlocks 2 2 2 := by
  constructor
  · intro i; simp [repeatedBlocks]
  · intro X _; simp [indexedSubsetDegree, repeatedBlocks]

/-- Off-diagonal excess retains all three equal occurrences before subtracting the seed. -/
theorem repeated_excess : natExcess repeatedBlocks (fun _ => 1) {0} {1}=2 := by decide

theorem repeated_gram (X Y : subsets (Fin 2) 1) :
    (incidence repeatedBlocks (subsets (Fin 2) 1) *
      (incidence repeatedBlocks (subsets (Fin 2) 1)).transpose) X Y = 3 := by
  rw [incidence_gram_entry]
  simp [indexedSubsetDegree, repeatedBlocks]

end CoveringDesigns.MulticoverLargeDefect.Examples
