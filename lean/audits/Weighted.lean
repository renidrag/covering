import CoveringDesigns.Weighted
import CoveringDesigns.Foundations.StandardAxioms

/-! Independent full contracts for general weighted foundations and pair integration. -/
open Finset Matrix CoveringDesigns CoveringDesigns.HorsleySingh
universe u v

#print CoveringDesigns.Family
#print CoveringDesigns.HorsleySingh.multiplicity
#print CoveringDesigns.HorsleySingh.diagonal
#print CoveringDesigns.HorsleySingh.excess
#print CoveringDesigns.HorsleySingh.baseline

#check (Weighted.diagonal_add_posDef_of_weighted_row_sum_lt :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (ρ c : ι → ℝ) (E : Matrix ι ι ℝ),
    (∀ i j, E i j = E j i) → (∀ i j, 0 ≤ E i j) → (∀ i, 0 < c i) →
    (∀ i, ∑ j, E i j*c j < ρ i*c i) → (Matrix.diagonal ρ+E).PosDef)

#check (Weighted.gram_card_le_of_weighted_row_sum_lt :
  ∀ {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (X : Matrix ι κ ℝ) (ρ c : ι → ℝ) (E P : Matrix ι ι ℝ),
    (∀ i j, E i j = E j i) → (∀ i j, 0 ≤ E i j) → (∀ i, 0 < c i) →
    (∀ i, ∑ j, E i j*c j < ρ i*c i) → P.PosSemidef →
    X*X.transpose = Matrix.diagonal ρ+E+P → Fintype.card ι ≤ Fintype.card κ)

#check (Weighted.card_le_two_levels_add_highExcess :
  ∀ {ι : Type u} (S : Finset ι) (u : ι → ℕ) {m : ℕ},
    (∀ x ∈ S, m ≤ u x) → S.card ≤ (S.filter (fun x => u x=m)).card +
      (S.filter (fun x => u x=m+1)).card + Equality.highExcess S u m)

#check (Weighted.two_level_bound :
  ∀ {ι : Type u} (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {α β : ℝ},
    0 ≤ β → 2*β ≤ α → (∀ x ∈ S, m ≤ u x) → (∑ x ∈ S, u x)=K*b →
    α*(S.filter (fun x => u x=m)).card + β*(S.filter (fun x => u x=m+1)).card ≤ b →
    (S.card : ℝ)*((m : ℝ)*(α-β)+α) ≤ (b : ℝ)*((K : ℝ)*(α-β)+1))

#check (Weighted.two_level_denominator_pos : ∀ (K : ℕ) {α β : ℝ},
  0 ≤ β → 2*β ≤ α → 0 < (K : ℝ)*(α-β)+1)

#check (Weighted.two_level_ratio :
  ∀ {ι : Type u} (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {α β : ℝ},
    0 ≤ β → 2*β ≤ α → (∀ x ∈ S, m ≤ u x) → (∑ x ∈ S, u x)=K*b →
    α*(S.filter (fun x => u x=m)).card + β*(S.filter (fun x => u x=m+1)).card ≤ b →
    (S.card : ℝ)*((m : ℝ)*(α-β)+α)/((K : ℝ)*(α-β)+1) ≤ b)

#check (Weighted.two_level_ceiling :
  ∀ {ι : Type u} (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {α β : ℝ},
    0 ≤ β → 2*β ≤ α → (∀ x ∈ S, m ≤ u x) → (∑ x ∈ S, u x)=K*b →
    α*(S.filter (fun x => u x=m)).card + β*(S.filter (fun x => u x=m+1)).card ≤ b →
    ⌈(S.card : ℝ)*((m : ℝ)*(α-β)+α)/((K : ℝ)*(α-β)+1)⌉₊ ≤ b)

#check (Weighted.two_level_q :
  ∀ {ι : Type u} (S : Finset ι) (u : ι → ℕ) {m K b q : ℕ},
    2 ≤ q → (∀ x ∈ S, m ≤ u x) → (∑ x ∈ S, u x)=K*b →
    q*(S.filter (fun x => u x=m)).card + (S.filter (fun x => u x=m+1)).card ≤ q*b →
    (S.card : ℤ)*(((q : ℤ)-1)*m+q) ≤ (b : ℤ)*(((q : ℤ)-1)*K+q))

#check (Weighted.selected_pairs_card_le :
  ∀ {α : Type u} [Fintype α] [DecidableEq α] {C : Family α} {b₂ b₃ b₄ : ℕ},
    b₄ ≤ b₃ → (∀ X : Finset α, X.card=3 → b₃ ≤ multiplicity C X) →
    (∀ X : Finset α, X.card=4 → b₄ ≤ multiplicity C X) →
    ∀ (S : Finset (Finset α)), (∀ X ∈ S, X.card=2) → ∀ c : S → ℝ,
    (∀ X, 0 < c X) →
    (∀ X : S, ∑ Y : S, (excess C b₃ b₄ X.val Y.val : ℝ)*c Y <
      ((diagonal b₂ b₃ b₄ + multiplicity C X.val-b₂ : ℤ) : ℝ)*c X) → S.card ≤ C.card)

namespace CoveringDesigns.AuditWeighted

/-- Explicit finite-family contract: no hidden uniformity or coverage assumption. -/
theorem selected_pairs_explicit {α : Type u} [Fintype α] [DecidableEq α]
    {C : Finset (Finset α)} {b₂ b₃ b₄ : ℕ} (h₄₃ : b₄ ≤ b₃)
    (h₃ : ∀ X : Finset α, X.card=3 → b₃ ≤ (C.filter (X ⊆ ·)).card)
    (h₄ : ∀ X : Finset α, X.card=4 → b₄ ≤ (C.filter (X ⊆ ·)).card)
    (S : Finset (Finset α)) (hS : ∀ X ∈ S, X.card=2)
    (c : S → ℝ) (hc : ∀ X, 0 < c X)
    (hd : ∀ X : S, ∑ Y : S,
      ((if X.val=Y.val then (0 : ℤ) else
        ((C.filter (X.val ∪ Y.val ⊆ ·)).card : ℤ) -
          ((b₄ : ℤ)+((b₃ : ℤ)-b₄)*(X.val ∩ Y.val).card) : ℤ) : ℝ)*c Y <
      (((b₂ : ℤ)-2*b₃+b₄+(C.filter (X.val ⊆ ·)).card-b₂ : ℤ) : ℝ)*c X) :
    S.card ≤ C.card := by
  exact Weighted.selected_pairs_card_le h₄₃ h₃ h₄ S hS c hc hd

end CoveringDesigns.AuditWeighted

#check (Weighted.Examples.unit_weights :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (ρ : ι → ℝ) (E : Matrix ι ι ℝ),
    (∀ i j, E i j=E j i) → (∀ i j, 0 ≤ E i j) →
    (∀ i, ∑ j, E i j < ρ i) → (Matrix.diagonal ρ+E).PosDef)
#check (Weighted.Examples.weighted_two_by_two :
  (Matrix.diagonal ![(1 : ℝ),5]+!![0,2;2,0]).PosDef ∧
    ¬ (∑ j : Fin 2, (!![0,2;2,0] : Matrix (Fin 2) (Fin 2) ℝ) 0 j) < 1)
#check (Weighted.Examples.zero_excess :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (ρ : ι → ℝ),
    (∀ i, 0 < ρ i) → (Matrix.diagonal ρ+(0 : Matrix ι ι ℝ)).PosDef)
#check (Weighted.Examples.empty_matrix :
  (Matrix.diagonal (fun _ : Fin 0 => (0 : ℝ))+0).PosDef)
#check (Weighted.Examples.empty_selected_pairs :
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (C : Family α),
    (∅ : Finset (Finset α)).card ≤ C.card)
#check (Weighted.Examples.beta_zero :
  ∀ {ι : Type u} (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {α : ℝ},
    0 ≤ α → (∀ x ∈ S, m ≤ u x) → (∑ x ∈ S, u x)=K*b →
    α*(S.filter (fun x => u x=m)).card ≤ b →
    (S.card : ℝ)*((m : ℝ)*α+α) ≤ (b : ℝ)*((K : ℝ)*α+1))
#check (Weighted.Examples.alpha_eq_two_beta :
  ∀ {ι : Type u} (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {β : ℝ},
    0 ≤ β → (∀ x ∈ S, m ≤ u x) → (∑ x ∈ S, u x)=K*b →
    (2*β)*(S.filter (fun x => u x=m)).card + β*(S.filter (fun x => u x=m+1)).card ≤ b →
    (S.card : ℝ)*((m : ℝ)*β+2*β) ≤ (b : ℝ)*((K : ℝ)*β+1))
#check (Weighted.Examples.empty_counting :
  ∀ {ι : Type u} (_u : ι → ℕ) (m K : ℕ) {α β : ℝ}, 0 ≤ β → 2*β ≤ α →
    ⌈((∅ : Finset ι).card : ℝ)*((m : ℝ)*(α-β)+α)/((K : ℝ)*(α-β)+1)⌉₊ ≤ 0)

#guard_standard_axioms Weighted.diagonal_add_posDef_of_weighted_row_sum_lt
  Weighted.gram_card_le_of_weighted_row_sum_lt Weighted.card_le_two_levels_add_highExcess
  Weighted.two_level_bound Weighted.two_level_denominator_pos Weighted.two_level_ratio
  Weighted.two_level_ceiling Weighted.two_level_q Weighted.selected_pairs_card_le
  AuditWeighted.selected_pairs_explicit Weighted.Examples.unit_weights
  Weighted.Examples.weighted_two_by_two Weighted.Examples.zero_excess
  Weighted.Examples.empty_matrix Weighted.Examples.empty_selected_pairs
  Weighted.Examples.beta_zero Weighted.Examples.alpha_eq_two_beta Weighted.Examples.empty_counting
#print axioms CoveringDesigns.Weighted.diagonal_add_posDef_of_weighted_row_sum_lt
#print axioms CoveringDesigns.Weighted.gram_card_le_of_weighted_row_sum_lt
#print axioms CoveringDesigns.Weighted.card_le_two_levels_add_highExcess
#print axioms CoveringDesigns.Weighted.two_level_bound
#print axioms CoveringDesigns.Weighted.two_level_denominator_pos
#print axioms CoveringDesigns.Weighted.two_level_ratio
#print axioms CoveringDesigns.Weighted.two_level_ceiling
#print axioms CoveringDesigns.Weighted.two_level_q
#print axioms CoveringDesigns.Weighted.selected_pairs_card_le
#print axioms CoveringDesigns.AuditWeighted.selected_pairs_explicit
#print axioms CoveringDesigns.Weighted.Examples.unit_weights
#print axioms CoveringDesigns.Weighted.Examples.weighted_two_by_two
#print axioms CoveringDesigns.Weighted.Examples.zero_excess
#print axioms CoveringDesigns.Weighted.Examples.empty_matrix
#print axioms CoveringDesigns.Weighted.Examples.empty_selected_pairs
#print axioms CoveringDesigns.Weighted.Examples.beta_zero
#print axioms CoveringDesigns.Weighted.Examples.alpha_eq_two_beta
#print axioms CoveringDesigns.Weighted.Examples.empty_counting
