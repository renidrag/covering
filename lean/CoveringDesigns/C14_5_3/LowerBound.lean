import CoveringDesigns.C14_5_3.ParentCharges
import CoveringDesigns.C14_5_3.FourMinimum
import CoveringDesigns.Multicover.Family

/-! The unconditional lower bound. Completion28 is intentionally downstream. -/
namespace CoveringDesigns.C14_5_3
open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

noncomputable def minimumPoints (B : ι → Finset α) : Finset α :=
  univ.filter (fun x => indexedDegree B x = 13)

theorem forty_has_minimum {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hn : Fintype.card ι = 40) :
    ∃ x, indexedDegree B x = 13 := by
  classical
  by_contra hh
  push Not at hh
  have hf (x : α) : 14 ≤ indexedDegree B x := by
    have := point_floor hv hB x
    have := hh x
    omega
  have hs := Multicover.degree_sum_of_uniform hB.1
  rw [hn] at hs
  have hhcount : (highPoints B).card ≤ 4 := by
    have hp (x : α) : 14 + (if 15 ≤ indexedDegree B x then 1 else 0) ≤ indexedDegree B x := by
      have := hf x
      split_ifs <;> omega
    have hsum := sum_le_sum (s := univ) (fun x _ => hp x)
    simp only [sum_add_distrib,sum_const,card_univ,Nat.nsmul_eq_mul,hv,hs,sum_boole] at hsum
    change 14 * 14 + (highPoints B).card ≤ 5 * 40 at hsum
    omega
  have hpartition : (middlePoints B).card + (highPoints B).card = 14 := by
    have hp (x : α) : (if indexedDegree B x = 14 then 1 else 0) +
        (if 15 ≤ indexedDegree B x then 1 else 0) = 1 := by
      have := hf x
      split_ifs <;> omega
    have hsum := sum_congr (s₁ := univ) rfl (fun x _ => hp x)
    simpa [sum_add_distrib,middlePoints,highPoints,hv] using hsum
  have hirr := forty_irredundant hv hB hn
  have hc := distinct_private_triples hv hB hirr
  have hchoose : ((highPoints B).card).choose 3 ≤ 4 := by
    calc
      _ ≤ (4:ℕ).choose 3 := Nat.choose_le_choose 3 hhcount
      _ = 4 := by decide
  have hm := middle_le_twice_special hv hB hirr
  omega

theorem degree_profile_bound {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hn : Fintype.card ι = 40) :
    210 ≤ 200 + 2 * (minimumPoints B).card + (middlePoints B).card := by
  classical
  have hp (x : α) : 15 ≤ indexedDegree B x +
      2 * (if indexedDegree B x = 13 then 1 else 0) +
      (if indexedDegree B x = 14 then 1 else 0) := by
    have := point_floor hv hB x
    split_ifs <;> omega
  have hs := sum_le_sum (s := univ) (fun x _ => hp x)
  rw [sum_add_distrib,sum_add_distrib,←mul_sum,Multicover.degree_sum_of_uniform hB.1,hn] at hs
  simpa [sum_boole,minimumPoints,middlePoints,hv] using hs

theorem not_forty {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hn : Fintype.card ι = 40) : False := by
  classical
  obtain ⟨x,hx⟩ := forty_has_minimum hv hB hn
  have hs := minimum_special_count hv hB hn hx
  have hm := middle_le_twice_special hv hB (forty_irredundant hv hB hn)
  have hm2 : (middlePoints B).card ≤ 2 := by omega
  have hZ : ∀ z ∈ minimumPoints B, indexedDegree B z = 13 := fun z hz => (mem_filter.mp hz).2
  have hz := minimum_points_le_four hv hB hZ
  have hb := degree_profile_bound hv hB hn
  have hz4 : (minimumPoints B).card = 4 := by omega
  obtain ⟨p,hp,hp16⟩ := four_minimum_forces_sixteen hv hB hZ hz4
  have hpoint (q : α) : 15 + (if q = p then 1 else 0) ≤ indexedDegree B q +
      2 * (if indexedDegree B q = 13 then 1 else 0) +
      (if indexedDegree B q = 14 then 1 else 0) := by
    have := point_floor hv hB q
    by_cases hq : q = p
    · subst q
      simp only [ite_true]
      split_ifs <;> omega
    · simp only [hq,ite_false,Nat.add_zero]
      split_ifs <;> omega
  have hsum := sum_le_sum (s := univ) (fun q _ => hpoint q)
  simp only [sum_add_distrib,←mul_sum,Multicover.degree_sum_of_uniform hB.1,hn] at hsum
  have hsum' : 211 ≤ 200 + 2 * (minimumPoints B).card + (middlePoints B).card := by
    simpa [sum_boole,minimumPoints,middlePoints,hv] using hsum
  omega

/-- Indexed occurrences may repeat. All structural facts are derived internally. -/
theorem indexed_lower_bound {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) : 41 ≤ Fintype.card ι := by
  have h40 := lower_bound_40 hv hB
  have hne : Fintype.card ι ≠ 40 := fun hn => not_forty hv hB hn
  omega

/-- The ordinary-family contract assumes only the covering condition. -/
theorem lower_bound {C : Family α} (hv : Fintype.card α = 14)
    (hC : IsCover C 5 3) : 41 ≤ C.card := by
  classical
  have h := indexed_lower_bound hv ((Multicover.ofFamily_isCover_one C 5 3).mpr hC)
  simpa only [Multicover.ofFamily_card] using h

end CoveringDesigns.C14_5_3
