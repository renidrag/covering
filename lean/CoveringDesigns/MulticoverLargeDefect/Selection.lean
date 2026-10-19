import CoveringDesigns.LargeDefect.Algebra
import CoveringDesigns.MulticoverIncidence.Matrices
import CoveringDesigns.CaroTuza.Selection

/-! Occurrence-indexed full-excess-graph selection for Horsley–Singh Theorem 15.
Natural edges are identified with signed excess only under proved
nonnegativity. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.MulticoverLargeDefect
open Finset HigherIncidence MulticoverIncidence LargeDefect
universe u w
variable {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι]

def natExcess (B : ι → Finset α) (b : ℕ → ℕ) (X Y : Finset α) : ℕ :=
  (excess B b X Y).toNat

omit [Fintype α] in
theorem natExcess_cast {B : ι → Finset α} {b : ℕ → ℕ} {s : ℕ}
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    {X Y : Finset α} (hX : X.card=s) (hY : Y.card=s) :
    (natExcess B b X Y : ℤ) = excess B b X Y :=
  Int.toNat_of_nonneg (excess_nonneg hb hX hY)

omit [Fintype α] in
theorem natExcess_sum_cast {B : ι → Finset α} {b : ℕ → ℕ} {s : ℕ}
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    {X : Finset α} (hX : X.card=s) (S : Finset (Finset α))
    (hS : ∀ Y ∈ S, Y.card=s) :
    ((∑ Y ∈ S, natExcess B b X Y : ℕ) : ℤ) = ∑ Y ∈ S, excess B b X Y := by
  push_cast
  exact sum_congr rfl (fun Y hY => natExcess_cast hb hX (hS Y hY))

/-- The full natural degree agrees with the existing exact signed identity. -/
theorem natExcess_degree {B : ι → Finset α} {b : ℕ → ℕ} {k s : ℕ}
    (hu : Multicover.Uniform B k)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    {X : Finset α} (hX : X.card=s) :
    ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℤ) =
      ((indexedSubsetDegree B X : ℤ)-b s)*((k.choose s : ℤ)-1)+
        defect (Fintype.card α) k s b := by
  rw [natExcess_sum_cast hb hX _ (fun Y hY => mem_subsets.mp hY)]
  exact excess_row_sum hu b hX

/-- Any selected set with internal excess below a natural threshold at most
the diagonal allowance satisfies the indexed rank obstruction. -/
theorem independent_card_le {B : ι → Finset α} {b : ℕ → ℕ} {s a : ℕ}
    (hac : (a : ℤ) ≤ coefficient s b s)
    (hc : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=s)
    (hdeg : ∀ X ∈ S, ∑ Y ∈ S, natExcess B b X Y < a) :
    S.card ≤ Fintype.card ι := by
  apply rank_obstruction hc hb S hS
  intro X hx
  have hd : ((∑ Y ∈ S, natExcess B b X Y : ℕ) : ℤ) < a := by
    exact_mod_cast hdeg X hx
  rw [natExcess_sum_cast hb (hS X hx) S hS] at hd
  have hX := hS X hx
  have hm : b s ≤ indexedSubsetDegree B X := by
    simpa [hX] using hb X (by omega) (by omega)
  omega

/-- Any positive selection threshold at most the diagonal coefficient gives
a potential bound, with no assumption that either low class is nonempty. -/
theorem potential_bound {B : ι → Finset α} {b : ℕ → ℕ} {s a : ℕ}
    (ha : 0 < a) (hac : (a : ℤ) ≤ coefficient s b s)
    (hc : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z) :
    (∑ X ∈ subsets α s,
      CaroTuza.f a ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℝ)) ≤ Fintype.card ι := by
  obtain ⟨S, hS, hdeg, hsize⟩ := CaroTuza.exists_nat_selection ha (natExcess B b)
    (subsets α s) (fun X _ Y _ => by simp only [natExcess, excess_comm B b X Y])
    (fun X _ => by simp [natExcess, MulticoverIncidence.excess])
  have hScard : ∀ X ∈ S, X.card=s := fun X hx => mem_subsets.mp (hS hx)
  have hr := independent_card_le hac hc hb S hScard hdeg
  exact (Nat.ceil_le.mp hsize).trans (by exact_mod_cast hr)

/-- Caro–Tuza on the full excess graph, followed by the selected-subset rank
obstruction. This is the selection inequality used by Theorem 15. -/
theorem selection_bound {B : ι → Finset α} {b : ℕ → ℕ} {k s : ℕ}
    (hu : Multicover.Uniform B k) (hK : 0 < k.choose s)
    (hc : ∀ j < s, 0 ≤ coefficient s b j)
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (ha : 1 ≤ coefficient s b s)
    (had : coefficient s b s ≤ defect (Fintype.card α) k s b) :
    alpha (coefficient s b s) (defect (Fintype.card α) k s b) *
        ((subsets α s).filter (indexedSubsetDegree B · = b s)).card +
      beta (k.choose s) (coefficient s b s) (defect (Fintype.card α) k s b) *
        ((subsets α s).filter (indexedSubsetDegree B · = b s+1)).card ≤ Fintype.card ι := by
  let a := (coefficient s b s).toNat
  have haI : (a : ℤ) = coefficient s b s := Int.toNat_of_nonneg (by omega)
  have hap : 0 < a := by omega
  have haR : (a : ℝ) = (coefficient s b s : ℝ) := by exact_mod_cast haI
  have hadR : (a : ℝ) ≤ (defect (Fintype.card α) k s b : ℝ) := by
    exact_mod_cast (show (a : ℤ) ≤ defect (Fintype.card α) k s b by omega)
  have hkR : (1 : ℝ) ≤ k.choose s := by exact_mod_cast hK
  have hlow (X : Finset α) (hX : X.card=s) (hm : indexedSubsetDegree B X=b s) :
      CaroTuza.f a ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℝ) =
        alpha (coefficient s b s) (defect (Fintype.card α) k s b) := by
    have he := natExcess_degree hu hb hX
    rw [hm, sub_self, zero_mul, zero_add] at he
    have heR : ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℝ) =
        (defect (Fintype.card α) k s b : ℝ) := by exact_mod_cast he
    rw [heR, CaroTuza.f_high hap hadR, haR]
    rfl
  have hnext (X : Finset α) (hX : X.card=s) (hm : indexedSubsetDegree B X=b s+1) :
      CaroTuza.f a ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℝ) =
        beta (k.choose s) (coefficient s b s) (defect (Fintype.card α) k s b) := by
    have he : ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℤ) =
        defect (Fintype.card α) k s b + (k.choose s : ℤ)-1 := by
      rw [natExcess_degree hu hb hX, hm, Nat.cast_add, Nat.cast_one]
      ring
    have heR : ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℝ) =
        (defect (Fintype.card α) k s b : ℝ) + (k.choose s : ℝ)-1 := by exact_mod_cast he
    rw [heR, CaroTuza.f_high hap (by linarith), haR]
    simp only [beta, sub_add_cancel]
  have hp := potential_bound hap haI.le hc hb
  apply le_trans _ hp
  have hs := sum_le_sum (s := subsets α s) (f := fun X =>
      (if indexedSubsetDegree B X=b s then
        alpha (coefficient s b s) (defect (Fintype.card α) k s b) else 0) +
      (if indexedSubsetDegree B X=b s+1 then
        beta (k.choose s) (coefficient s b s) (defect (Fintype.card α) k s b) else 0))
    (g := fun X => CaroTuza.f a ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℝ))
    (fun X hx => by
      have hX := mem_subsets.mp hx
      by_cases h0 : indexedSubsetDegree B X=b s
      · have h1 : indexedSubsetDegree B X ≠ b s+1 := by omega
        simp only [ite_eq_left h0, ite_eq_right h1, add_zero, hlow X hX h0, le_refl]
      · by_cases h1 : indexedSubsetDegree B X=b s+1
        · simp only [ite_eq_right h0, ite_eq_left h1, zero_add, hnext X hX h1, le_refl]
        · simp only [ite_eq_right h0, ite_eq_right h1, zero_add]
          exact CaroTuza.f_nonneg hap (Nat.cast_nonneg _))
  simpa only [sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm] using hs

end CoveringDesigns.MulticoverLargeDefect
