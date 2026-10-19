import CoveringDesigns.TwoKMinusC

open CoveringDesigns CoveringDesigns.TwoKMinusC
open Finset HigherIncidence
set_option linter.unusedVariables false

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.degree
#print CoveringDesigns.star
#print CoveringDesigns.Multicover.ofFamily
#print CoveringDesigns.TwoKMinusC.seed
#print CoveringDesigns.TwoKMinusC.offsetDefect
#print CoveringDesigns.TwoKMinusC.numerator
#print CoveringDesigns.TwoKMinusC.denominator
#print CoveringDesigns.TwoKMinusC.Q

namespace CoveringDesigns.AuditTwoKMinusC

theorem exactness_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α=2*k-2) (hk : 36≤k) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card=k) ∧
      (∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) ∧ C.card=14) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card=k) →
      (∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) → 14≤C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hlower⟩ := OffsetTwo.exactness hv hk
  exact ⟨⟨C,hC.1,hC.2,hcard⟩, fun C hu hc => hlower C ⟨hu,hc⟩⟩

theorem lower_thirteen_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α=2*k-2) (hk : 18≤k)
    (C : Finset (Finset α)) (hu : ∀ B ∈ C, B.card=k)
    (hc : ∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) : 13≤C.card :=
  OffsetTwo.thirteen_le_card hv hk ⟨hu,hc⟩

theorem actual_floors_explicit {α : Type*} [Fintype α] [DecidableEq α]
    {c k : ℕ} (C : Finset (Finset α))
    (hv : Fintype.card α+c=2*k) (hc : 2≤c) (hck : c<k) (hk : 6<k)
    (hu : ∀ B ∈ C, B.card=k)
    (hp : ∀ x, 6≤(C.filter (fun B => x∈B)).card)
    (hpq : ∀ x y, x≠y → 3≤(C.filter (fun B => x∈B ∧ y∈B)).card) :
    Nat.ceil (Q c k)≤C.card := by
  apply actual_floors_bound hv hc hck hk hu hp
  intro x y hxy
  simpa only [degree, star, filter_filter] using hpq x y hxy

/-- Ordinary blocks become one occurrence each, without any duplication. -/
theorem occurrence_transport {α : Type*} [DecidableEq α] (C : Family α) (k : ℕ) :
    Fintype.card C=C.card ∧
    (Multicover.Uniform (Multicover.ofFamily C) k ↔ Uniform C k) ∧
    (∀ X, indexedSubsetDegree (Multicover.ofFamily C) X=HorsleySingh.multiplicity C X) :=
  ⟨Multicover.ofFamily_card C, Multicover.ofFamily_uniform C k,
    Multicover.ofFamily_subsetDegree C⟩

end CoveringDesigns.AuditTwoKMinusC

-- Full types of every new public declaration follow.

#check (@CoveringDesigns.TwoKMinusC.coefficient_zero : coefficient 1 seed 0 = 3)

#check (@CoveringDesigns.TwoKMinusC.coefficient_one : coefficient 1 seed 1 = 3)

#check (@CoveringDesigns.TwoKMinusC.defect_eq : ∀ {v c k : ℕ} (hv : v+c=2*k) (hck : c<k),
    defect v k 1 seed = offsetDefect c)

#check (@CoveringDesigns.TwoKMinusC.offsetDefect_ge : ∀ {c : ℕ} (hc : 2≤c),
    3 ≤ offsetDefect c)

#check (@CoveringDesigns.TwoKMinusC.denominator_pos : ∀ {c k : ℕ} (hc : 2≤c),
    0 < denominator c k)

#check (@CoveringDesigns.TwoKMinusC.value_eq_Q : ∀ {v c k : ℕ} (hv : v+c=2*k) (hc : 2≤c) (hck : c<k),
    MulticoverLargeDefect.value v k 1 seed = Q c k)

#check (@CoveringDesigns.TwoKMinusC.Q_nonneg : ∀ {c k : ℕ} (hc : 2≤c) (hck : c<k) (hk : 6<k),
    0 ≤ Q c k)

#check (@CoveringDesigns.TwoKMinusC.Q_le_iff : ∀ {c k : ℕ} {n : ℝ} (hc : 2≤c),
    Q c k ≤ n ↔ numerator c k ≤ n * denominator c k)

#check (@CoveringDesigns.TwoKMinusC.ceil_Q_le_iff : ∀ {c k n : ℕ} (hc : 2≤c),
    Nat.ceil (Q c k) ≤ n ↔ numerator c k ≤ (n : ℝ)*denominator c k)

#check (@CoveringDesigns.TwoKMinusC.actual_subset_floors : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}
    (hpoint : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (Z : Finset α) (hlo : 1 ≤ Z.card) (hhi : Z.card ≤ 2),
    seed Z.card ≤ indexedSubsetDegree (Multicover.ofFamily C) Z)

#check (@CoveringDesigns.TwoKMinusC.actual_floors_bound : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {c k : ℕ}
    (hv : Fintype.card α+c=2*k) (hc : 2≤c) (hck : c<k) (hk : 6<k)
    (hu : Uniform C k) (hpoint : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y),
    Nat.ceil (Q c k) ≤ C.card)

#check (@CoveringDesigns.TwoKMinusC.actual_floors_real : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {c k : ℕ}
    (hv : Fintype.card α+c=2*k) (hc : 2≤c) (hck : c<k) (hk : 6<k)
    (hu : Uniform C k) (hpoint : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y),
    Q c k ≤ (C.card : ℝ))

#check (@CoveringDesigns.TwoKMinusC.actual_floors_inequality : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {c k : ℕ}
    (hv : Fintype.card α+c=2*k) (hc : 2≤c) (hck : c<k) (hk : 6<k)
    (hu : Uniform C k) (hpoint : ∀ x, 6 ≤ degree C x)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y),
    numerator c k ≤ (C.card : ℝ)*denominator c k)

#check (@CoveringDesigns.TwoKMinusC.Q_two : ∀ (k : ℕ),
    Q 2 k = 2*((k : ℝ)-1)*(7*(k : ℝ)-3)/((k : ℝ)^2+k+6))

#check (@CoveringDesigns.TwoKMinusC.twelve_lt_Q_two : ∀ {k : ℕ} (hk : 18≤k),
    12 < Q 2 k)

#check (@CoveringDesigns.TwoKMinusC.thirteen_lt_Q_two : ∀ {k : ℕ} (hk : 36≤k),
    13 < Q 2 k)

#check (@CoveringDesigns.TwoKMinusC.OffsetTwo.thirteen_le_card : ∀ {α : Type*} [Fintype α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α=2*k-2) (hk : 18≤k) (hC : IsCover C k 3),
    13 ≤ C.card)

#check (@CoveringDesigns.TwoKMinusC.OffsetTwo.fourteen_le_card : ∀ {α : Type*} [Fintype α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α=2*k-2) (hk : 36≤k) (hC : IsCover C k 3),
    14 ≤ C.card)

#check (@CoveringDesigns.TwoKMinusC.OffsetTwo.exactness : ∀ {α : Type*} [Fintype α] {k : ℕ} (hv : Fintype.card α=2*k-2) (hk : 36≤k),
    (∃ C : Family α, IsCover C k 3 ∧ C.card=14) ∧
    (∀ C : Family α, IsCover C k 3 → 14≤C.card))

#check (@CoveringDesigns.TwoKMinusC.OffsetTwo.covering_number : ∀ {k : ℕ} (hk : 36≤k),
    (∃ C : Family (Fin (2*k-2)), IsCover C k 3 ∧ C.card=14) ∧
    (∀ C : Family (Fin (2*k-2)), IsCover C k 3 → 14≤C.card))

#check (@CoveringDesigns.TwoKMinusC.OffsetTwo.interval_34_18_3_on : ∀ {α : Type*} [Fintype α] (hv : Fintype.card α=34),
    (∃ C : Family α, IsCover C 18 3 ∧ C.card≤14) ∧
    (∀ C : Family α, IsCover C 18 3 → 13≤C.card))

#check (@CoveringDesigns.TwoKMinusC.OffsetTwo.exactness_70_36_3_on : ∀ {α : Type*} [Fintype α] (hv : Fintype.card α=70),
    (∃ C : Family α, IsCover C 36 3 ∧ C.card=14) ∧
    (∀ C : Family α, IsCover C 36 3 → 14≤C.card))

#guard_standard_axioms CoveringDesigns.TwoKMinusC.coefficient_zero
#print axioms CoveringDesigns.TwoKMinusC.coefficient_zero

#guard_standard_axioms CoveringDesigns.TwoKMinusC.coefficient_one
#print axioms CoveringDesigns.TwoKMinusC.coefficient_one

#guard_standard_axioms CoveringDesigns.TwoKMinusC.defect_eq
#print axioms CoveringDesigns.TwoKMinusC.defect_eq

#guard_standard_axioms CoveringDesigns.TwoKMinusC.offsetDefect_ge
#print axioms CoveringDesigns.TwoKMinusC.offsetDefect_ge

#guard_standard_axioms CoveringDesigns.TwoKMinusC.denominator_pos
#print axioms CoveringDesigns.TwoKMinusC.denominator_pos

#guard_standard_axioms CoveringDesigns.TwoKMinusC.value_eq_Q
#print axioms CoveringDesigns.TwoKMinusC.value_eq_Q

#guard_standard_axioms CoveringDesigns.TwoKMinusC.Q_nonneg
#print axioms CoveringDesigns.TwoKMinusC.Q_nonneg

#guard_standard_axioms CoveringDesigns.TwoKMinusC.Q_le_iff
#print axioms CoveringDesigns.TwoKMinusC.Q_le_iff

#guard_standard_axioms CoveringDesigns.TwoKMinusC.ceil_Q_le_iff
#print axioms CoveringDesigns.TwoKMinusC.ceil_Q_le_iff

#guard_standard_axioms CoveringDesigns.TwoKMinusC.actual_subset_floors
#print axioms CoveringDesigns.TwoKMinusC.actual_subset_floors

#guard_standard_axioms CoveringDesigns.TwoKMinusC.actual_floors_bound
#print axioms CoveringDesigns.TwoKMinusC.actual_floors_bound

#guard_standard_axioms CoveringDesigns.TwoKMinusC.actual_floors_real
#print axioms CoveringDesigns.TwoKMinusC.actual_floors_real

#guard_standard_axioms CoveringDesigns.TwoKMinusC.actual_floors_inequality
#print axioms CoveringDesigns.TwoKMinusC.actual_floors_inequality

#guard_standard_axioms CoveringDesigns.TwoKMinusC.Q_two
#print axioms CoveringDesigns.TwoKMinusC.Q_two

#guard_standard_axioms CoveringDesigns.TwoKMinusC.twelve_lt_Q_two
#print axioms CoveringDesigns.TwoKMinusC.twelve_lt_Q_two

#guard_standard_axioms CoveringDesigns.TwoKMinusC.thirteen_lt_Q_two
#print axioms CoveringDesigns.TwoKMinusC.thirteen_lt_Q_two

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.thirteen_le_card
#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.thirteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.fourteen_le_card
#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.fourteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.exactness
#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.exactness

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.covering_number
#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.covering_number

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.interval_34_18_3_on
#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.interval_34_18_3_on

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.exactness_70_36_3_on
#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.exactness_70_36_3_on

#guard_standard_axioms CoveringDesigns.AuditTwoKMinusC.exactness_explicit
#print axioms CoveringDesigns.AuditTwoKMinusC.exactness_explicit

#guard_standard_axioms CoveringDesigns.AuditTwoKMinusC.lower_thirteen_explicit
#print axioms CoveringDesigns.AuditTwoKMinusC.lower_thirteen_explicit

#guard_standard_axioms CoveringDesigns.AuditTwoKMinusC.actual_floors_explicit
#print axioms CoveringDesigns.AuditTwoKMinusC.actual_floors_explicit

#guard_standard_axioms CoveringDesigns.AuditTwoKMinusC.occurrence_transport
#print axioms CoveringDesigns.AuditTwoKMinusC.occurrence_transport

-- Fixed arithmetic is kernel checked; adjacent failures are method limitations.
example : Q 2 17 = (464 : ℝ)/39 := by norm_num [Q, numerator, denominator, offsetDefect]
example : Q 2 18 = (697 : ℝ)/58 := by norm_num [Q, numerator, denominator, offsetDefect]
example : Q 2 35 = (8228 : ℝ)/633 := by norm_num [Q, numerator, denominator, offsetDefect]
example : Q 2 36 = (2905 : ℝ)/223 := by norm_num [Q, numerator, denominator, offsetDefect]
-- Lowest k allowed by the adapter and the k=d+1 fallback boundary.
example : Q 2 7 = (276 : ℝ)/31 := by norm_num [Q, numerator, denominator, offsetDefect]
example : Q 4 10 = (1168 : ℝ)/185 := by norm_num [Q, numerator, denominator, offsetDefect]
example : HigherIncidence.defect 16 10 1 seed=9 := by norm_num [HigherIncidence.defect, seed, sum_range_succ]
example : (∃ C : Family (Fin 34), IsCover C 18 3 ∧ C.card≤14) ∧
    (∀ C : Family (Fin 34), IsCover C 18 3 → 13≤C.card) :=
  OffsetTwo.interval_34_18_3_on (by simp)
example : (∃ C : Family (Fin 70), IsCover C 36 3 ∧ C.card=14) ∧
    (∀ C : Family (Fin 70), IsCover C 36 3 → 14≤C.card) :=
  OffsetTwo.exactness_70_36_3_on (by simp)

example : Q 2 17 < 12 ∧ Nat.ceil (Q 2 17)=12 := by
  constructor
  · norm_num [Q, numerator, denominator, offsetDefect]
  · apply (Nat.ceil_eq_iff (by decide : 12 ≠ 0)).mpr
    norm_num [Q, numerator, denominator, offsetDefect]
example : 12 < Q 2 18 ∧ Nat.ceil (Q 2 18)=13 := by
  constructor
  · norm_num [Q, numerator, denominator, offsetDefect]
  · apply (Nat.ceil_eq_iff (by decide : 13 ≠ 0)).mpr
    norm_num [Q, numerator, denominator, offsetDefect]
example : Q 2 35 < 13 ∧ Nat.ceil (Q 2 35)=13 := by
  constructor
  · norm_num [Q, numerator, denominator, offsetDefect]
  · apply (Nat.ceil_eq_iff (by decide : 13 ≠ 0)).mpr
    norm_num [Q, numerator, denominator, offsetDefect]
example : 13 < Q 2 36 ∧ Nat.ceil (Q 2 36)=14 := by
  constructor
  · norm_num [Q, numerator, denominator, offsetDefect]
  · apply (Nat.ceil_eq_iff (by decide : 14 ≠ 0)).mpr
    norm_num [Q, numerator, denominator, offsetDefect]

-- The actual adapter accepts its minimum k and the fallback boundary.
example {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}
    (hv : Fintype.card α=12) (hu : Uniform C 7)
    (hp : ∀ x, 6≤degree C x)
    (hpq : ∀ x y, x≠y → 3≤degree (star C x) y) : 9≤C.card := by
  have h := actual_floors_bound (c := 2) (by omega : Fintype.card α+2=2*7)
    (by norm_num) (by norm_num) (by norm_num) hu hp hpq
  apply le_trans ?_ h
  apply (Nat.add_one_le_ceil_iff (n := 8)).mpr
  norm_num [Q, numerator, denominator, offsetDefect]
example {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}
    (hv : Fintype.card α=16) (hu : Uniform C 10)
    (hp : ∀ x, 6≤degree C x)
    (hpq : ∀ x y, x≠y → 3≤degree (star C x) y) : 7≤C.card := by
  have h := actual_floors_bound (c := 4) (by omega : Fintype.card α+4=2*10)
    (by norm_num) (by norm_num) (by norm_num) hu hp hpq
  apply le_trans ?_ h
  apply (Nat.add_one_le_ceil_iff (n := 6)).mpr
  norm_num [Q, numerator, denominator, offsetDefect]
