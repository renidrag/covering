import CoveringDesigns.TwoKMinusTwoEquality

open CoveringDesigns CoveringDesigns.TwoKMinusTwo
open Finset Matrix Module
set_option linter.unusedVariables false

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.minimumPoints
#print CoveringDesigns.TwoKMinusTwo.lowIncidence
#print CoveringDesigns.TwoKMinusTwo.lowExcess
#print CoveringDesigns.TwoKMinusTwo.deficit

namespace CoveringDesigns.AuditTwoKMinusTwoEquality

/-- Full arbitrary-label exactness, with both covering conditions exposed. -/
theorem exactness_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 40 ≤ k) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = k) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 14) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = k) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 14 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hlower⟩ := TwoKMinusTwoEquality.exactness hv hk
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hlower C ⟨hu,hc⟩⟩

/-- Lower thirteen has no unmentioned rank or support assumption. -/
theorem lower_thirteen_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 19 ≤ k)
    (C : Finset (Finset α)) (hu : ∀ B ∈ C, B.card = k)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) :
    13 ≤ C.card := by
  classical
  exact TwoKMinusTwoEquality.thirteen_le_card hv hk ⟨hu,hc⟩

/-- At 36 points the exposed conclusion is only the interval 13--14. -/
theorem interval_explicit {α : Type*} [Fintype α]
    (hv : Fintype.card α = 36) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 19) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card ≤ 14) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 19) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 13 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hlower⟩ := TwoKMinusTwoEquality.interval_36_19_3_on hv
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hlower C ⟨hu,hc⟩⟩

end CoveringDesigns.AuditTwoKMinusTwoEquality

-- Full public contracts: all quantifiers and structural hypotheses retained.
-- BoundaryRank/Equality.lean

#check (@CoveringDesigns.BoundaryRank.component_pairing : ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (G : SimpleGraph ι) (Z : Finset ι) (K : Submodule ℝ (ι → ℝ))
    (hneigh : ∀ i ∈ Z, ∃ j, G.Adj i j)
    (hzero : ∀ x ∈ K, ∀ i, i ∉ Z → x i = 0)
    (hedge : ∀ x ∈ K, ∀ i j, G.Adj i j → x i + x j = 0)
    (hcard : Fintype.card ι = 2 * Fintype.card κ)
    (hlower : Fintype.card κ ≤ finrank ℝ K),
    Z = univ ∧ ∃ e : κ × Bool ≃ ι,
      ∀ i j, G.Adj (e i) (e j) → i.1 = j.1)

#check (@CoveringDesigns.BoundaryRank.gram_equality : ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (R : Matrix ι κ ℝ) (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ)
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    (hgram : R * R.transpose = Matrix.diagonal (fun _ => ρ) + E + P)
    (hcard : Fintype.card ι = 2 * Fintype.card κ),
    (∀ i, δ i = 0) ∧ ∃ e : κ × Bool ≃ ι,
      (∀ i j, i ≠ j → ∀ b c, E (e (i,b)) (e (j,c)) = 0) ∧
      (∀ i, E (e (i,false)) (e (i,true)) = ρ))

-- TwoKMinusTwoEquality/Matrix.lean

#check (@CoveringDesigns.TwoKMinusTwoEquality.constant_posSemidef : ∀ {ι : Type*} [Fintype ι] (lam : ℝ) (hlam : 0 ≤ lam),
    (Matrix.of (fun (_ _ : ι) => lam)).PosSemidef)

#check (@CoveringDesigns.TwoKMinusTwoEquality.rows_eq_of_gram : ∀ {ι κ : Type*} [Fintype κ] (R : Matrix ι κ ℝ) (i j : ι) (r : ℝ)
    (hi : (R * R.transpose) i i = r)
    (hj : (R * R.transpose) j j = r)
    (hij : (R * R.transpose) i j = r),
    ∀ x, R i x = R j x)

#check (@CoveringDesigns.TwoKMinusTwoEquality.square_parameters : ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℝ) (r lam : ℝ)
    (hlam : 0 ≤ lam) (hlt : lam < r) (hb : 0 < Fintype.card κ)
    (hrow : ∀ i, ∑ j, M i j = r)
    (hgram : M * M.transpose =
      Matrix.diagonal (fun _ => r-lam) + Matrix.of (fun _ _ => lam)),
    (∀ j, ∑ i, M i j = r) ∧ lam * ((Fintype.card κ : ℝ)-1) = r*(r-1))

#check (@CoveringDesigns.TwoKMinusTwoEquality.boundary_parameter : ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (R : Matrix ι κ ℝ) (r lam : ℝ)
    (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hlam : 0 ≤ lam) (hlt : lam < r) (hb : 0 < Fintype.card κ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hz : ∀ i, E i i = 0) (hδ : ∀ i, 0 ≤ δ i)
    (hbalance : ∀ i, (∑ j, E i j) + δ i = r-lam)
    (hrow : ∀ i, ∑ j, R i j = r)
    (hgram : R * R.transpose =
      Matrix.diagonal (fun _ => r-lam) + E + Matrix.of (fun _ _ => lam))
    (hcard : Fintype.card ι = 2 * Fintype.card κ),
    (∀ i, δ i = 0) ∧
    (∃ e : κ × Bool ≃ ι,
      (∀ i j, R (e (i,false)) j = R (e (i,true)) j) ∧
      (∀ i j, i ≠ j → (R * R.transpose) (e (i,false)) (e (j,false)) = lam)) ∧
    lam * ((Fintype.card κ : ℝ)-1) = r*(r-1))

-- TwoKMinusTwoEquality/Rigidity.lean

#check (@CoveringDesigns.TwoKMinusTwoEquality.low_row_sum : ∀ {α : Type*} [Fintype α] [DecidableEq α] (C : Family α) (x : Low C),
    ∑ B : C, lowIncidence C x B = (6 : ℝ))

#check (@CoveringDesigns.TwoKMinusTwoEquality.low_equality_rigidity : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hu : Uniform C k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (heq : (minimumPoints C 6).card = 2*C.card),
    C.card = 11 ∧ (∀ x : Low C, deficit C x = 0) ∧
      ∃ e : C × Bool ≃ Low C, ∀ i B : C,
        ((e (i,false)).val ∈ B.val ↔ (e (i,true)).val ∈ B.val))

#check (@CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_low_equality : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hu : Uniform C k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (heq : (minimumPoints C 6).card = 2*C.card),
    C.card = 11)

-- TwoKMinusTwoEquality/Bounds.lean

#check (@CoveringDesigns.TwoKMinusTwoEquality.low_count_eq_of_tight : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k) (hC : IsCover C k 3)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (htight : 14*(k-1) = (k+2)*C.card),
    (minimumPoints C 6).card = 2*C.card)

#check (@CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_tight : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k) (hC : IsCover C k 3)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (htight : 14*(k-1) = (k+2)*C.card),
    C.card = 11)

#check (@CoveringDesigns.TwoKMinusTwoEquality.lower_bound_36_19_3 : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}
    (hv : Fintype.card α = 36) (hC : IsCover C 19 3),
    13 ≤ C.card)

#check (@CoveringDesigns.TwoKMinusTwoEquality.lower_bound_78_40_3 : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}
    (hv : Fintype.card α = 78) (hC : IsCover C 40 3),
    14 ≤ C.card)

#check (@CoveringDesigns.TwoKMinusTwoEquality.thirteen_le_card : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 19 ≤ k)
    (hC : IsCover C k 3),
    13 ≤ C.card)

#check (@CoveringDesigns.TwoKMinusTwoEquality.fourteen_le_card : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 40 ≤ k)
    (hC : IsCover C k 3),
    14 ≤ C.card)

-- TwoKMinusTwoEquality.lean

#check (@CoveringDesigns.TwoKMinusTwoEquality.exactness : ∀ {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 40 ≤ k),
    (∃ C : Family α, IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C k 3 → 14 ≤ C.card))

#check (@CoveringDesigns.TwoKMinusTwoEquality.covering_number : ∀ {k : ℕ} (hk : 40 ≤ k),
    (∃ C : Family (Fin (2*k-2)), IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin (2*k-2)), IsCover C k 3 → 14 ≤ C.card))

#check (@CoveringDesigns.TwoKMinusTwoEquality.interval_36_19_3_on : ∀ {α : Type*} [Fintype α]
    (hv : Fintype.card α = 36),
    (∃ C : Family α, IsCover C 19 3 ∧ C.card ≤ 14) ∧
    (∀ C : Family α, IsCover C 19 3 → 13 ≤ C.card))

#check (@CoveringDesigns.TwoKMinusTwoEquality.exactness_78_40_3_on : ∀ {α : Type*} [Fintype α]
    (hv : Fintype.card α = 78),
    (∃ C : Family α, IsCover C 40 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C 40 3 → 14 ≤ C.card))

#guard_standard_axioms CoveringDesigns.BoundaryRank.component_pairing
#print axioms CoveringDesigns.BoundaryRank.component_pairing

#guard_standard_axioms CoveringDesigns.BoundaryRank.gram_equality
#print axioms CoveringDesigns.BoundaryRank.gram_equality

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.constant_posSemidef
#print axioms CoveringDesigns.TwoKMinusTwoEquality.constant_posSemidef

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.rows_eq_of_gram
#print axioms CoveringDesigns.TwoKMinusTwoEquality.rows_eq_of_gram

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.square_parameters
#print axioms CoveringDesigns.TwoKMinusTwoEquality.square_parameters

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.boundary_parameter
#print axioms CoveringDesigns.TwoKMinusTwoEquality.boundary_parameter

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.low_row_sum
#print axioms CoveringDesigns.TwoKMinusTwoEquality.low_row_sum

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.low_equality_rigidity
#print axioms CoveringDesigns.TwoKMinusTwoEquality.low_equality_rigidity

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_low_equality
#print axioms CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_low_equality

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.low_count_eq_of_tight
#print axioms CoveringDesigns.TwoKMinusTwoEquality.low_count_eq_of_tight

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_tight
#print axioms CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_tight

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.lower_bound_36_19_3
#print axioms CoveringDesigns.TwoKMinusTwoEquality.lower_bound_36_19_3

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.lower_bound_78_40_3
#print axioms CoveringDesigns.TwoKMinusTwoEquality.lower_bound_78_40_3

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.thirteen_le_card
#print axioms CoveringDesigns.TwoKMinusTwoEquality.thirteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.fourteen_le_card
#print axioms CoveringDesigns.TwoKMinusTwoEquality.fourteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.exactness
#print axioms CoveringDesigns.TwoKMinusTwoEquality.exactness

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.covering_number
#print axioms CoveringDesigns.TwoKMinusTwoEquality.covering_number

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.interval_36_19_3_on
#print axioms CoveringDesigns.TwoKMinusTwoEquality.interval_36_19_3_on

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.exactness_78_40_3_on
#print axioms CoveringDesigns.TwoKMinusTwoEquality.exactness_78_40_3_on

#guard_standard_axioms CoveringDesigns.AuditTwoKMinusTwoEquality.exactness_explicit
#print axioms CoveringDesigns.AuditTwoKMinusTwoEquality.exactness_explicit

#guard_standard_axioms CoveringDesigns.AuditTwoKMinusTwoEquality.lower_thirteen_explicit
#print axioms CoveringDesigns.AuditTwoKMinusTwoEquality.lower_thirteen_explicit

#guard_standard_axioms CoveringDesigns.AuditTwoKMinusTwoEquality.interval_explicit
#print axioms CoveringDesigns.AuditTwoKMinusTwoEquality.interval_explicit

-- The zero-lambda endpoint is consistent with a one-column identity matrix.
example : (∀ j : Fin 1, ∑ i : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℝ) i j = 1) ∧
    (0 : ℝ) * ((Fintype.card (Fin 1) : ℝ)-1) = 1*(1-1) := by
  apply TwoKMinusTwoEquality.square_parameters (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 0
  · norm_num
  · norm_num
  · norm_num
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  · ext i j; simp

example : (∀ i : Fin 0, (0 : ℝ) = 0) ∧
    ∃ e : Fin 0 × Bool ≃ Fin 0,
      (∀ i j, i ≠ j → ∀ b c, (0 : Matrix (Fin 0) (Fin 0) ℝ) (e (i,b)) (e (j,c)) = 0) ∧
      (∀ i, (0 : Matrix (Fin 0) (Fin 0) ℝ) (e (i,false)) (e (i,true)) = 1) := by
  apply BoundaryRank.gram_equality (0 : Matrix (Fin 0) (Fin 0) ℝ) 1 0 (fun _ => 0) (P := 0)
  · norm_num
  · simp
  · simp
  · simp
  · simp
  · intro i; exact Fin.elim0 i
  · exact Matrix.PosSemidef.zero
  · ext i; exact Fin.elim0 i
  · simp
