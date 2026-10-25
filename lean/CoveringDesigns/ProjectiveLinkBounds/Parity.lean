import CoveringDesigns.ProjectiveLinkBounds.Incidence

/-! Odd secants include tangents. All triples below are distinct point subsets,
not line occurrences. No coordinatisation is used. -/
namespace CoveringDesigns.ProjectiveLinkBounds
open Finset Internal
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

def collinearTriples (L : ι → Finset α) (A : Finset α) : Finset (Finset α) :=
  (A.powersetCard 3).filter (fun T => 0 < indexedSubsetDegree L T)

theorem collinear_count {L : ι → Finset α} {q : ℕ}
    (hL : ExactDesign.IsDesign L (q+1) 2 1) (A : Finset α) :
    (collinearTriples L A).card = ∑ i, ((L i ∩ A).card).choose 3 := by
  rw [← trace_count, collinearTriples, card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro T hT
  have hm := exact_multiplicity_le_one hL (T := T)
    (by have := (mem_powersetCard.mp hT).2; omega)
  split_ifs <;> omega

private theorem outside_odd_secant {L : ι → Finset α} {q : ℕ}
    (ho : Odd q) (hL : ExactDesign.IsDesign L (q+1) 2 1)
    {A : Finset α} (hA : A.card = q+2) {y : α} (hy : y ∉ A) :
    ∃ i, y ∈ L i ∧ Odd (L i ∩ A).card := by
  classical
  by_contra hn
  have heven (i : {i // y ∈ L i}) : 2 ∣ (L i.val ∩ A).card := by
    apply Even.two_dvd
    apply Nat.not_odd_iff_even.mp
    exact fun h => hn ⟨i.val,i.property,h⟩
  let D := fun i : {i // y ∈ L i} => L i.val
  have hs : (∑ i, (D i ∩ A).card) = q+2 := by
    rw [intersection_sum]
    have hd (x : α) (hx : x ∈ A) : indexedDegree D x = 1 := by
      rw [degree_through_point]
      exact hL.2 _ (by simp [show y ≠ x from fun h => hy (h ▸ hx)])
    rw [sum_const_nat hd]
    simp [hA]
  have hdiv : 2 ∣ ∑ i, (D i ∩ A).card := dvd_sum (fun i _ => heven i)
  rw [hs] at hdiv
  rcases hdiv with ⟨s,hs⟩
  rcases ho with ⟨r,hr⟩
  omega

private theorem outside_charge {L : ι → Finset α} {q : ℕ}
    (ho : Odd q) (hv : Fintype.card α = pointCount q)
    (hL : ExactDesign.IsDesign L (q+1) 2 1)
    {A : Finset α} (hA : A.card = q+2) :
    q^2-1 ≤ ∑ i, if Odd (L i ∩ A).card then q+1-(L i ∩ A).card else 0 := by
  classical
  let U := (univ : Finset α) \ A
  have hl (y : α) (hy : y ∈ U) :
      1 ≤ (univ.filter (fun i => y ∈ L i ∧ Odd (L i ∩ A).card)).card := by
    obtain ⟨i,hi,ho⟩ := outside_odd_secant ho hL hA (mem_sdiff.mp hy).2
    exact card_pos.mpr ⟨i, by simp [hi,ho]⟩
  have hs := sum_le_sum hl
  have he : (∑ y ∈ U, (univ.filter (fun i => y ∈ L i ∧ Odd (L i ∩ A).card)).card) =
      ∑ i, if Odd (L i ∩ A).card then q+1-(L i ∩ A).card else 0 := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    simp only [sum_const, Nat.nsmul_eq_mul, mul_one]
    apply sum_congr rfl
    intro i _
    by_cases hi : Odd (L i ∩ A).card
    · simp only [hi, and_true, if_true]
      rw [← sum_filter, ← card_eq_sum_ones]
      have hf : U.filter (fun y => y ∈ L i) = L i \ A := by
        ext y; simp [U]; tauto
      rw [hf, card_sdiff, hL.1 i, inter_comm A (L i)]
    · simp [hi]
  rw [he] at hs
  have hc : U.card = q^2-1 := by
    change ((univ : Finset α) \ A).card = q^2-1
    rw [card_sdiff_of_subset (subset_univ A), card_univ, hv, hA]
    unfold pointCount
    omega
  simpa [hc] using hs

private theorem secant_coefficient {q i : ℕ} (hq : 3 ≤ q) (hi : i ≤ q+1) :
    (q : ℤ)*i*((i : ℤ)-2) +
      (if Odd i then (q+1-i : ℕ) else 0 : ℕ) ≤
        (4*(q : ℤ)-2)*(i.choose 3 : ℤ) := by
  by_cases hs : i < 3
  · interval_cases i <;> norm_num [Nat.choose, Nat.odd_iff, show q+1-1=q by omega]
  · have hi3 : (3 : ℤ) ≤ i := by omega
    have hq3 : (3 : ℤ) ≤ q := by omega
    have ho : (if Odd i then (q+1-i : ℕ) else 0 : ℕ) ≤ q+1-i := by
      split_ifs <;> omega
    have ho' : ((if Odd i then (q+1-i : ℕ) else 0 : ℕ) : ℤ) ≤
        (q : ℤ)+1-i := by exact_mod_cast ho
    have hc := choose_three_int i
    have hqc := congrArg (fun z : ℤ => (2*(q : ℤ)-1)*z) hc
    have hf : 0 ≤ ((i : ℤ)-1)*((i : ℤ)-3)*((2*(q : ℤ)-1)*i-q-1) := by
      apply mul_nonneg (mul_nonneg (by omega) (by omega))
      nlinarith
    nlinarith

/-- The outside-point odd-secant count in an arbitrary indexed exact pair design. -/
theorem parity_bound {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {L : ι → Finset α} (hv : Fintype.card α = pointCount q)
    (hL : ExactDesign.IsDesign L (q+1) 2 1) {A : Finset α} (hA : A.card = q+2) :
    q^2-1 ≤ (4*q-2)*(collinearTriples L A).card := by
  classical
  have hp : (∑ i, ((L i ∩ A).card).choose 2) = (q+2).choose 2 := by
    rw [← trace_count, sum_const_nat (fun P hP => hL.2 P (mem_powersetCard.mp hP).2)]
    simp [hA]
  have hx : (∑ i, (L i ∩ A).card) = (q+2)*(q+1) := by
    rw [intersection_sum, sum_const_nat (fun x _ => exact_point_count (by omega) hv hL x)]
    simp [hA]
  have hz : (∑ i, ((L i ∩ A).card : ℤ)*((L i ∩ A).card-2)) = 0 := by
    calc
      _ = ∑ i, (2*(((L i ∩ A).card).choose 2 : ℤ) - (L i ∩ A).card) := by
        apply sum_congr rfl
        intro i _
        nlinarith [choose_two_int (L i ∩ A).card]
      _ = 2*(∑ i, ((L i ∩ A).card).choose 2 : ℕ) - (∑ i, (L i ∩ A).card : ℕ) := by
        simp [sum_sub_distrib, mul_sum]
      _ = 0 := by
        rw [hp,hx]
        have hc := choose_two_int (q+2)
        push_cast at hc ⊢
        nlinarith
  have hc := sum_le_sum (s := (univ : Finset ι)) (fun i _ =>
    secant_coefficient hq (show (L i ∩ A).card ≤ q+1 by
      simpa [hL.1 i] using card_le_card (inter_subset_left (s₁ := L i) (s₂ := A))))
  have hout := outside_charge ho hv hL hA
  have he : (∑ i, (q : ℤ)*(L i ∩ A).card*((L i ∩ A).card-2)) = 0 := by
    simpa only [mul_assoc, ← mul_sum, hz, mul_zero] using congrArg (fun z : ℤ => q*z) hz
  rw [sum_add_distrib, he, zero_add, ← mul_sum] at hc
  rw [collinear_count hL]
  zify [show 1 ≤ q^2 by nlinarith, show 2 ≤ 4*q by omega] at hout ⊢
  push_cast at hc
  exact hout.trans hc

theorem collinear_lower_bound {q : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    {L : ι → Finset α} (hv : Fintype.card α = pointCount q)
    (hL : ExactDesign.IsDesign L (q+1) 2 1) {A : Finset α} (hA : A.card = q+2) :
    collinearFloor q ≤ (collinearTriples L A).card := by
  rw [← collinearFloor_eq hq ho]
  exact (Schoenheim.ceilDiv_le_iff (by omega)).mpr (parity_bound hq ho hv hL hA)

end CoveringDesigns.ProjectiveLinkBounds
