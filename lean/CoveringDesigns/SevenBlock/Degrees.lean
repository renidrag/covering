import CoveringDesigns.SevenBlock.Indexed
import CoveringDesigns.SevenBlock.SupportSlack
import CoveringDesigns.Equality.FiniteSum

/-! Degree profiles of seven-block pair coverings. All support fibres retain
their actual points. The preliminary excess split is private bookkeeping. -/
namespace CoveringDesigns.SevenBlock
open Finset
universe u v
variable {V : Type u} {I : Type v} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def pointSupport (B : I → Finset V) (x : V) : Finset I := univ.filter fun i => x ∈ B i

@[simp] theorem mem_pointSupport (B : I → Finset V) (x : V) (i : I) :
    i ∈ pointSupport B x ↔ x ∈ B i := by simp [pointSupport]

@[simp] theorem pointSupport_card (B : I → Finset V) (x : V) :
    (pointSupport B x).card = indexedDegree B x := rfl

theorem pointSupport_pair (B : I → Finset V) (x y : V) :
    (pointSupport B x ∩ pointSupport B y).card = indexedSubsetDegree B {x,y} := by
  congr 1
  ext i
  simp [pointSupport, indexedSubsetDegree, insert_subset_iff, singleton_subset_iff]

theorem pointSupports_meet {B : I → Finset V} {k : ℕ}
    (h : Multicover.IsCover B k 2 1) (x y : V) (hxy : x ≠ y) :
    (pointSupport B x ∩ pointSupport B y).Nonempty := by
  obtain ⟨i,hi⟩ := (Multicover.covers_one_iff B 2).mp h.2 {x,y} (card_pair hxy)
  exact ⟨i, by simpa only [mem_inter, mem_pointSupport] using
    (show x ∈ B i ∧ y ∈ B i from ⟨hi (by simp), hi (by simp)⟩)⟩

/-- Restrict actual point identities, without deduplicating their supports. -/
def remainingSupports (B : I → Finset V) (E : Finset V) :
    {x : V // x ∉ E} → Finset I := fun x => pointSupport B x.val

private theorem remaining_row (B : I → Finset V) (E : Finset V) (i : I) :
    indexedDegree (remainingSupports B E) i = (B i \ E).card := by
  have he : univ.filter (fun x : {x : V // x ∉ E} => i ∈ remainingSupports B E x) =
      (B i).subtype (· ∉ E) := by
    ext x
    simp [remainingSupports]
  unfold indexedDegree
  rw [he, card_subtype]
  congr 1
  ext x
  simp

private theorem twice_choose (n : ℕ) : 2 * (n.choose 2 : ℤ) = (n : ℤ) * (n-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    nlinarith

private theorem delete_one_moment {B : I → Finset V} {k : ℕ}
    (hu : Multicover.Uniform B (k+1)) (p : V) :
    (∑ i, ((indexedDegree (remainingSupports B {p}) i).choose 2 : ℤ)) =
      (Fintype.card I : ℤ) * ((k+1).choose 2 : ℤ) - (indexedDegree B p : ℤ) * k := by
  have hterm (i : I) : ((indexedDegree (remainingSupports B {p}) i).choose 2 : ℤ) =
      ((k+1).choose 2 : ℤ) - (k : ℤ) * if p ∈ B i then 1 else 0 := by
    rw [remaining_row, sdiff_singleton_eq_erase]
    by_cases hp : p ∈ B i
    · rw [card_erase_of_mem hp, hu]
      simp only [Nat.add_sub_cancel, if_pos hp, mul_one]
      have hh := Nat.choose_succ_succ k 1
      change (k+1).choose 2 = k.choose 1 + k.choose 2 at hh
      rw [Nat.choose_one_right] at hh
      have hc : ((k+1).choose 2 : ℤ) = (k : ℤ) + (k.choose 2 : ℤ) := by exact_mod_cast hh
      omega
    · rw [erase_eq_of_notMem hp, hu]
      simp [hp]
  simp_rw [hterm]
  rw [sum_sub_distrib, ← mul_sum]
  have hp : (∑ i, if p ∈ B i then (1 : ℤ) else 0) = indexedDegree B p := by
    simp only [indexedDegree, card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  rw [hp]
  simp [mul_comm]

private theorem initial_profiles {a : ℕ} (ha : 1 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) :
    (∃ p, indexedDegree B p = 5 ∧ ∀ x, x ≠ p → indexedDegree B x = 3) ∨
    (∃ p q, p ≠ q ∧ indexedDegree B p = 4 ∧ indexedDegree B q = 4 ∧
      ∀ x, x ≠ p → x ≠ q → indexedDegree B x = 3) := by
  have he : ∑ x, (indexedDegree B x - 3) = 2 := by
    have hc := Equality.excess_sum_cast (S := (univ : Finset V))
      (u := indexedDegree B) (m := 3) (fun x _ => degree_floor ha hv h x)
    have hd : (∑ x, (indexedDegree B x : ℤ)) = (3*a+2 : ℕ) * (7 : ℤ) := by
      exact_mod_cast (Multicover.degree_sum_of_uniform h.1).trans (by rw [hi])
    rw [hd] at hc
    simp only [card_univ, hv] at hc
    omega
  rcases Equality.budget_two he with ⟨p,_,hp,hr⟩ | ⟨p,_,q,_,hpq,hp,hq,hr⟩
  · left
    refine ⟨p, by have := degree_floor ha hv h p; omega, ?_⟩
    intro x hx
    have := hr x (mem_univ _) hx
    have := degree_floor ha hv h x
    omega
  · right
    refine ⟨p,q,hpq,by have := degree_floor ha hv h p; omega,
      by have := degree_floor ha hv h q; omega, ?_⟩
    intro x hxp hxq
    have := hr x (mem_univ _) hxp hxq
    have := degree_floor ha hv h x
    omega

private theorem no_degree_five {a : ℕ} (ha : 1 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) (p : V) (hp : indexedDegree B p = 5)
    (hrest : ∀ x, x ≠ p → indexedDegree B x = 3) : False := by
  let S := remainingSupports B {p}
  have hm : Fintype.card {x : V // x ∉ ({p} : Finset V)} = 7*a+3 := by
    rw [Multicover.subset_complement_card, card_singleton, hv]
    omega
  have hs : ∀ x, (S x).card = 3 := by
    intro x
    exact hrest x.val (by simpa using x.property)
  have hmeet : ∀ x y, x ≠ y → (S x ∩ S y).Nonempty := by
    intro x y hxy
    exact pointSupports_meet h x.val y.val (fun he => hxy (Subtype.ext he))
  have hdiv : Fintype.card {x : V // x ∉ ({p} : Finset V)} * Nat.choose 3 2 =
      (Fintype.card I).choose 2 * a + 9 := by
    rw [hm, hi]
    norm_num [show Nat.choose 7 2 = 21 by decide, show Nat.choose 3 2 = 3 by decide]
    omega
  have hd := support_imbalance_nonneg S 3 a 9 hs hdiv
  have ht := partial_overlap_nonneg S 3 hs hmeet
  have hid := support_slack_identity S 3 a 9
  have hrow := delete_one_moment (k := 3*a+1) (B := B) (by simpa [Nat.add_assoc] using h.1) p
  rw [hi, hp] at hrow
  have he : supportExcess S =
      7 * ((3*a+2).choose 2 : ℤ) - 5*(3*a+1 : ℕ) - ((7*a+3).choose 2 : ℤ) := by
    unfold supportExcess
    change (∑ i, ((indexedDegree (remainingSupports B {p}) i).choose 2 : ℤ)) - _ = _
    rw [hrow, hm]
    norm_num
  rw [he] at hid
  simp only [balancedMoment, hi] at hid
  norm_num [show Nat.choose 7 2 = 21 by decide] at hid
  have h₁ := twice_choose (3*a+2)
  have h₂ := twice_choose (7*a+3)
  have h₃ := twice_choose a
  push_cast at h₁ h₂ h₃ hid
  nlinarith

/-- Every seven-occurrence cover has exactly two degree-four points and all
other points have degree three. This holds already at a=1. -/
theorem covering_degree_profile {a : ℕ} (ha : 1 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) :
    ∃ p q, p ≠ q ∧ indexedDegree B p = 4 ∧ indexedDegree B q = 4 ∧
      ∀ x, x ≠ p → x ≠ q → indexedDegree B x = 3 := by
  rcases initial_profiles ha hv h hi with ⟨p,hp,hr⟩ | hh
  · exact (no_degree_five ha hv h hi p hp hr).elim
  · exact hh

private theorem delete_two_moment {B : I → Finset V} {k : ℕ}
    (hu : Multicover.Uniform B (k+2)) (p q : V) (hpq : p ≠ q) :
    (∑ i, ((indexedDegree (remainingSupports B {p,q}) i).choose 2 : ℤ)) =
      (Fintype.card I : ℤ) * ((k+2).choose 2 : ℤ) -
      (k+1 : ℤ) * ((indexedDegree B p : ℤ) + indexedDegree B q) +
      indexedSubsetDegree B {p,q} := by
  have hc₀ : ((k+1).choose 2 : ℤ) = (k : ℤ) + (k.choose 2 : ℤ) := by
    exact_mod_cast (show (k+1).choose 2 = k + k.choose 2 from
      by simpa using Nat.choose_succ_succ k 1)
  have hc₁ : ((k+2).choose 2 : ℤ) = (k+1 : ℤ) + ((k+1).choose 2 : ℤ) := by
    exact_mod_cast (show (k+2).choose 2 = k+1 + (k+1).choose 2 from
      by simpa [Nat.add_assoc] using Nat.choose_succ_succ (k+1) 1)
  have hterm (i : I) : ((indexedDegree (remainingSupports B {p,q}) i).choose 2 : ℤ) =
      ((k+2).choose 2 : ℤ) - (k+1 : ℤ) *
        ((if p ∈ B i then 1 else 0) + (if q ∈ B i then 1 else 0)) +
        (if p ∈ B i ∧ q ∈ B i then 1 else 0) := by
    rw [remaining_row]
    have hm : (B i ∩ {p,q}).card =
        (if p ∈ B i then 1 else 0) + (if q ∈ B i then 1 else 0) := by
      rw [inter_comm]
      by_cases hp : p ∈ B i <;> by_cases hq : q ∈ B i <;>
        simp [insert_inter, singleton_inter, hp, hq, hpq]
    have hr := card_sdiff_add_card_inter (B i) {p,q}
    rw [hu, hm] at hr
    by_cases hp : p ∈ B i <;> by_cases hq : q ∈ B i
    · have he : (B i \ {p,q}).card = k := by simp [hp,hq] at hr; omega
      rw [he]; simp [hp,hq]; omega
    · have he : (B i \ {p,q}).card = k+1 := by simp [hp,hq] at hr; omega
      rw [he]; simp [hp,hq]; omega
    · have he : (B i \ {p,q}).card = k+1 := by simp [hp,hq] at hr; omega
      rw [he]; simp [hp,hq]; omega
    · have he : (B i \ {p,q}).card = k+2 := by simp [hp,hq] at hr; omega
      rw [he]; simp [hp,hq]
  have hmark (x : V) : (∑ i, if x ∈ B i then (1 : ℤ) else 0) = indexedDegree B x := by
    simp only [indexedDegree, card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  have hpair : (∑ i, if p ∈ B i ∧ q ∈ B i then (1 : ℤ) else 0) =
      indexedSubsetDegree B {p,q} := by
    simp only [indexedSubsetDegree, card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, insert_subset_iff, singleton_subset_iff]
  simp_rw [hterm]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_add_distrib, hmark, hmark, hpair]
  simp

/-- Exact covering slack after removing the two actual degree-four points.
The third argument is their actual codegree, without a simplicity premise. -/
theorem covering_slack {a : ℕ} {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (hu : Multicover.Uniform B (3*a+2))
    (hi : Fintype.card I = 7) (p q : V) (hpq : p ≠ q)
    (hp : indexedDegree B p = 4) (hq : indexedDegree B q = 4) :
    partialOverlap (remainingSupports B {p,q}) 3 +
      2 * supportImbalance (remainingSupports B {p,q}) a 6 =
        3 * ((indexedSubsetDegree B {p,q} : ℤ) - 2) := by
  let S := remainingSupports B {p,q}
  have hm : Fintype.card {x : V // x ∉ ({p,q} : Finset V)} = 7*a+2 := by
    rw [Multicover.subset_complement_card, card_pair hpq, hv]
    omega
  have hid := support_slack_identity S 3 a 6
  have hr := delete_two_moment hu p q hpq
  rw [hi,hp,hq] at hr
  have he : supportExcess S =
      7 * ((3*a+2).choose 2 : ℤ) - (3*(a : ℤ)+1)*8 +
        indexedSubsetDegree B {p,q} - ((7*a+2).choose 2 : ℤ) := by
    unfold supportExcess
    change (∑ i, ((indexedDegree (remainingSupports B {p,q}) i).choose 2 : ℤ)) - _ = _
    rw [hr, hm]
    push_cast
    ring
  rw [he] at hid
  simp only [balancedMoment, hi] at hid
  norm_num [show Nat.choose 7 2 = 21 by decide] at hid
  have h₁ := twice_choose (3*a+2)
  have h₂ := twice_choose (7*a+2)
  have h₃ := twice_choose a
  push_cast at h₁ h₂ h₃ hid
  change partialOverlap S 3 + 2 * supportImbalance S a 6 = _
  nlinarith

#guard_standard_axioms pointSupport_pair pointSupports_meet covering_degree_profile covering_slack

end CoveringDesigns.SevenBlock
