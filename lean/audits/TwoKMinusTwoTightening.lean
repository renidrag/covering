import CoveringDesigns.TwoKMinusTwoTightening

section TighteningContracts
attribute [local instance] Classical.propDecidable
open Finset Matrix
open scoped BigOperators
set_option linter.unusedVariables false
universe tightening_u_1 tightening_u_2 tightening_u_3

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.TwoKMinusTwoTightening.regularHigh
#print CoveringDesigns.TwoKMinusTwoTightening.positiveDeficitCount
#print CoveringDesigns.TwoKMinusTwoTightening.supportVector
#print CoveringDesigns.BoundaryRank.centered

#check (@CoveringDesigns.BoundaryRank.kernel_sum_zero : ∀ {ι : Type tightening_u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (ρ : ℝ)
  (E : Matrix ι ι ℝ) (δ : ι → ℝ),
  0 < ρ →
    (∀ (i j : ι), E i j = E j i) →
      (∀ (i j : ι), 0 ≤ E i j) →
        (∀ (i : ι), 0 ≤ δ i) →
          (∀ (i : ι), ∑ j, E i j + δ i = ρ) →
            ∀ {x : ι → ℝ}, ((Matrix.diagonal fun x => ρ) + E).mulVec x = (0 : ι → ℝ) → ∑ i, x i = 0)
#guard_standard_axioms CoveringDesigns.BoundaryRank.kernel_sum_zero
#print axioms CoveringDesigns.BoundaryRank.kernel_sum_zero

#check (@CoveringDesigns.BoundaryRank.ker_add_constant_eq : ∀ {ι : Type tightening_u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι]
  (ρ lam : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ),
  0 < ρ →
    0 ≤ lam →
      (∀ (i j : ι), E i j = E j i) →
        (∀ (i j : ι), 0 ≤ E i j) →
          (∀ (i : ι), 0 ≤ δ i) →
            (∀ (i : ι), ∑ j, E i j + δ i = ρ) →
              ((Matrix.diagonal fun x => ρ) + E + Matrix.of fun x x_1 => lam).mulVecLin.ker =
                ((Matrix.diagonal fun x => ρ) + E).mulVecLin.ker)
#guard_standard_axioms CoveringDesigns.BoundaryRank.ker_add_constant_eq
#print axioms CoveringDesigns.BoundaryRank.ker_add_constant_eq

#check (@CoveringDesigns.BoundaryRank.gram_rank_budget : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} [inst : Fintype ι]
  [inst_1 : DecidableEq ι] [inst_2 : Fintype κ] (R : Matrix ι κ ℝ) (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ),
  0 < ρ →
    (∀ (i j : ι), E i j = E j i) →
      (∀ (i j : ι), 0 ≤ E i j) →
        (∀ (i : ι), E i i = 0) →
          (∀ (i : ι), 0 ≤ δ i) →
            (∀ (i : ι), ∑ j, E i j + δ i = ρ) →
              ∀ (P : Matrix ι ι ℝ),
                P.PosSemidef →
                  R * R.transpose = (Matrix.diagonal fun x => ρ) + E + P →
                    Fintype.card ι + (Finset.univ.filter (fun i => 0 < δ i)).card ≤ 2 * R.rank)
#guard_standard_axioms CoveringDesigns.BoundaryRank.gram_rank_budget
#print axioms CoveringDesigns.BoundaryRank.gram_rank_budget

#check (@CoveringDesigns.BoundaryRank.centered_mulVec_one : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} [inst : Fintype κ]
  (R : Matrix ι κ ℝ) (r : ℝ),
  0 < Fintype.card κ → (∀ (i : ι), ∑ j, R i j = r) → ((CoveringDesigns.BoundaryRank.centered R r).mulVec fun x => 1) = 0)
#guard_standard_axioms CoveringDesigns.BoundaryRank.centered_mulVec_one
#print axioms CoveringDesigns.BoundaryRank.centered_mulVec_one

#check (@CoveringDesigns.BoundaryRank.centered_gram : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} [inst : Fintype κ] (R : Matrix ι κ ℝ)
  (r : ℝ),
  0 < Fintype.card κ →
    (∀ (i : ι), ∑ j, R i j = r) →
      CoveringDesigns.BoundaryRank.centered R r * (CoveringDesigns.BoundaryRank.centered R r).transpose =
        R * R.transpose - Matrix.of fun x x_1 => r ^ 2 / ↑(Fintype.card κ))
#guard_standard_axioms CoveringDesigns.BoundaryRank.centered_gram
#print axioms CoveringDesigns.BoundaryRank.centered_gram

#check (@CoveringDesigns.BoundaryRank.centered_rank_eq : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} [inst : Fintype ι]
  [inst_1 : DecidableEq ι] [inst_2 : Fintype κ] (R : Matrix ι κ ℝ) (r ρ lam : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ),
  0 < ρ →
    0 ≤ lam →
      0 < Fintype.card κ →
        (∀ (i j : ι), E i j = E j i) →
          (∀ (i j : ι), 0 ≤ E i j) →
            (∀ (i : ι), 0 ≤ δ i) →
              (∀ (i : ι), ∑ j, E i j + δ i = ρ) →
                (∀ (i : ι), ∑ j, R i j = r) →
                  (R * R.transpose = (Matrix.diagonal fun x => ρ) + E + Matrix.of fun x x_1 => lam) →
                    r ^ 2 ≤ ↑(Fintype.card κ) * lam → (CoveringDesigns.BoundaryRank.centered R r).rank = R.rank)
#guard_standard_axioms CoveringDesigns.BoundaryRank.centered_rank_eq
#print axioms CoveringDesigns.BoundaryRank.centered_rank_eq

#check (@CoveringDesigns.BoundaryRank.one_le_corank_of_mulVec_one_eq_zero : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} [inst : Fintype κ]
  (T : Matrix ι κ ℝ), 0 < Fintype.card κ → (T.mulVec fun x => 1) = 0 → 1 ≤ Fintype.card κ - T.rank)
#guard_standard_axioms CoveringDesigns.BoundaryRank.one_le_corank_of_mulVec_one_eq_zero
#print axioms CoveringDesigns.BoundaryRank.one_le_corank_of_mulVec_one_eq_zero

#check (@CoveringDesigns.BoundaryRank.centered_completion : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} [inst : Fintype ι]
  [inst_1 : DecidableEq ι] [inst_2 : Fintype κ] (R : Matrix ι κ ℝ) (r ρ lam : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ),
  0 < ρ →
    0 ≤ lam →
      0 < Fintype.card κ →
        (∀ (i j : ι), E i j = E j i) →
          (∀ (i j : ι), 0 ≤ E i j) →
            (∀ (i : ι), E i i = 0) →
              (∀ (i : ι), 0 ≤ δ i) →
                (∀ (i : ι), ∑ j, E i j + δ i = ρ) →
                  (∀ (i : ι), ∑ j, R i j = r) →
                    (R * R.transpose = (Matrix.diagonal fun x => ρ) + E + Matrix.of fun x x_1 => lam) →
                      r ^ 2 ≤ ↑(Fintype.card κ) * lam →
                        (CoveringDesigns.BoundaryRank.centered R r).rank = R.rank ∧
                          ((CoveringDesigns.BoundaryRank.centered R r).mulVec fun x => 1) = 0 ∧
                            1 ≤ Fintype.card κ - R.rank ∧ Fintype.card ι + (Finset.univ.filter (fun i => 0 < δ i)).card ≤ 2 * R.rank)
#guard_standard_axioms CoveringDesigns.BoundaryRank.centered_completion
#print axioms CoveringDesigns.BoundaryRank.centered_completion

#check (@CoveringDesigns.BoundaryRank.completion_eq_of_corank_le_one : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} [Fintype ι]
  [inst : Fintype κ] (T : Matrix ι κ ℝ),
  (T.mulVec fun x => 1) = 0 →
    0 < Fintype.card κ →
      Fintype.card κ - T.rank ≤ 1 → ∀ {x y : κ → ℝ}, T.mulVec x = T.mulVec y → ∑ j, x j = ∑ j, y j → x = y)
#guard_standard_axioms CoveringDesigns.BoundaryRank.completion_eq_of_corank_le_one
#print axioms CoveringDesigns.BoundaryRank.completion_eq_of_corank_le_one

#check (@CoveringDesigns.BoundaryRank.binary_completion_eq_or_eq : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} {X : Type tightening_u_3} [Fintype ι]
  [inst : Fintype κ] (T : Matrix ι κ ℝ),
  (T.mulVec fun x => 1) = 0 →
    0 < Fintype.card κ →
      Fintype.card κ - T.rank ≤ 2 →
        ∀ (w : X → κ → ℝ),
          (∀ (x : X) (j : κ), w x j = 0 ∨ w x j = 1) →
            ∀ (a : ι → ℝ),
              (∀ (x : X), T.mulVec (w x) = a) →
                ∀ (h : ℝ), (∀ (x : X), ∑ j, w x j = h) → ∀ {x₀ x₁ : X}, w x₀ ≠ w x₁ → ∀ (x : X), w x = w x₀ ∨ w x = w x₁)
#guard_standard_axioms CoveringDesigns.BoundaryRank.binary_completion_eq_or_eq
#print axioms CoveringDesigns.BoundaryRank.binary_completion_eq_or_eq

#check (@CoveringDesigns.BoundaryRank.binary_completion_card_le_two : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} {X : Type tightening_u_3} [Fintype ι]
  [inst : Fintype κ] [inst_1 : Fintype X] (T : Matrix ι κ ℝ),
  (T.mulVec fun x => 1) = 0 →
    0 < Fintype.card κ →
      Fintype.card κ - T.rank ≤ 2 →
        ∀ (w : X → κ → ℝ),
          (∀ (x : X) (j : κ), w x j = 0 ∨ w x j = 1) →
            ∀ (a : ι → ℝ),
              (∀ (x : X), T.mulVec (w x) = a) →
                ∀ (h : ℝ), (∀ (x : X), ∑ j, w x j = h) → (Finset.image w Finset.univ).card ≤ 2)
#guard_standard_axioms CoveringDesigns.BoundaryRank.binary_completion_card_le_two
#print axioms CoveringDesigns.BoundaryRank.binary_completion_card_le_two

#check (@CoveringDesigns.BoundaryRank.completion_card_le_one : ∀ {ι : Type tightening_u_1} {κ : Type tightening_u_2} {X : Type tightening_u_3} [Fintype ι]
  [inst : Fintype κ] [inst_1 : Fintype X] (T : Matrix ι κ ℝ),
  (T.mulVec fun x => 1) = 0 →
    0 < Fintype.card κ →
      Fintype.card κ - T.rank ≤ 1 →
        ∀ (w : X → κ → ℝ) (a : ι → ℝ),
          (∀ (x : X), T.mulVec (w x) = a) →
            ∀ (h : ℝ), (∀ (x : X), ∑ j, w x j = h) → (Finset.image w Finset.univ).card ≤ 1)
#guard_standard_axioms CoveringDesigns.BoundaryRank.completion_card_le_one
#print axioms CoveringDesigns.BoundaryRank.completion_card_le_one

#check (@CoveringDesigns.BoundaryRank.indexed_pair_sum_of_uniform : ∀ {α : Type tightening_u_1} {ι : Type tightening_u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) {k : ℕ},
  (∀ (i : ι), (B i).card = k) →
    ∀ (x : α), ∑ y, CoveringDesigns.indexedSubsetDegree B {x, y} = k * CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.BoundaryRank.indexed_pair_sum_of_uniform
#print axioms CoveringDesigns.BoundaryRank.indexed_pair_sum_of_uniform

#check (@CoveringDesigns.BoundaryRank.indexed_clone_capacity_at : ∀ {α : Type tightening_u_1} {ι : Type tightening_u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) (F : Finset α) {k h lam : ℕ},
  (∀ (i : ι), (B i).card = k) →
    ∀ (x : α),
      CoveringDesigns.indexedDegree B x = h →
        (∀ y ∈ F, ∀ (i : ι), x ∈ B i ↔ y ∈ B i) →
          (∀ y ∉ F, lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
            lam * Fintype.card α + h * F.card ≤ h * k + lam * F.card)
#guard_standard_axioms CoveringDesigns.BoundaryRank.indexed_clone_capacity_at
#print axioms CoveringDesigns.BoundaryRank.indexed_clone_capacity_at

#check (@CoveringDesigns.BoundaryRank.indexed_clone_capacity : ∀ {α : Type tightening_u_1} {ι : Type tightening_u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) (F : Finset α) {k h lam : ℕ},
  (∀ (i : ι), (B i).card = k) →
    F.Nonempty →
      (∀ x ∈ F, CoveringDesigns.indexedDegree B x = h) →
        (∀ x ∈ F, ∀ y ∈ F, ∀ (i : ι), x ∈ B i ↔ y ∈ B i) →
          (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
            lam * Fintype.card α + h * F.card ≤ h * k + lam * F.card)
#guard_standard_axioms CoveringDesigns.BoundaryRank.indexed_clone_capacity
#print axioms CoveringDesigns.BoundaryRank.indexed_clone_capacity

#check (@CoveringDesigns.BoundaryRank.indexed_clone_card_le_five : ∀ {α : Type tightening_u_1} {ι : Type tightening_u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) (F : Finset α),
  Fintype.card α = 32 →
    (∀ (i : ι), (B i).card = 17) →
      (∀ x ∈ F, CoveringDesigns.indexedDegree B x = 7) →
        (∀ x ∈ F, ∀ y ∈ F, ∀ (i : ι), x ∈ B i ↔ y ∈ B i) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) → F.card ≤ 5)
#guard_standard_axioms CoveringDesigns.BoundaryRank.indexed_clone_card_le_five
#print axioms CoveringDesigns.BoundaryRank.indexed_clone_card_le_five

#check (@CoveringDesigns.BoundaryRank.indexed_clone_card_le_ten : ∀ {α : Type tightening_u_1} {ι : Type tightening_u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) (F : Finset α),
  Fintype.card α = 68 →
    (∀ (i : ι), (B i).card = 35) →
      (∀ x ∈ F, CoveringDesigns.indexedDegree B x = 7) →
        (∀ x ∈ F, ∀ y ∈ F, ∀ (i : ι), x ∈ B i ↔ y ∈ B i) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) → F.card ≤ 10)
#guard_standard_axioms CoveringDesigns.BoundaryRank.indexed_clone_card_le_ten
#print axioms CoveringDesigns.BoundaryRank.indexed_clone_card_le_ten

#check (@CoveringDesigns.BoundaryRank.family_clone_capacity : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (C : CoveringDesigns.Family α) (F : Finset α) {k h lam : ℕ},
  CoveringDesigns.Uniform C k →
    F.Nonempty →
      (∀ x ∈ F, CoveringDesigns.degree C x = h) →
        (∀ x ∈ F, ∀ y ∈ F, ∀ B ∈ C, x ∈ B ↔ y ∈ B) →
          (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
            lam * Fintype.card α + h * F.card ≤ h * k + lam * F.card)
#guard_standard_axioms CoveringDesigns.BoundaryRank.family_clone_capacity
#print axioms CoveringDesigns.BoundaryRank.family_clone_capacity

#check (@CoveringDesigns.BoundaryRank.clone_card_le_five : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (C : CoveringDesigns.Family α) (F : Finset α),
  Fintype.card α = 32 →
    CoveringDesigns.Uniform C 17 →
      (∀ x ∈ F, CoveringDesigns.degree C x = 7) →
        (∀ x ∈ F, ∀ y ∈ F, ∀ B ∈ C, x ∈ B ↔ y ∈ B) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) → F.card ≤ 5)
#guard_standard_axioms CoveringDesigns.BoundaryRank.clone_card_le_five
#print axioms CoveringDesigns.BoundaryRank.clone_card_le_five

#check (@CoveringDesigns.BoundaryRank.clone_card_le_ten : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (C : CoveringDesigns.Family α) (F : Finset α),
  Fintype.card α = 68 →
    CoveringDesigns.Uniform C 35 →
      (∀ x ∈ F, CoveringDesigns.degree C x = 7) →
        (∀ x ∈ F, ∀ y ∈ F, ∀ B ∈ C, x ∈ B ↔ y ∈ B) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) → F.card ≤ 10)
#guard_standard_axioms CoveringDesigns.BoundaryRank.clone_card_le_ten
#print axioms CoveringDesigns.BoundaryRank.clone_card_le_ten

#check (@CoveringDesigns.BoundaryRank.card_le_mul_image_card : ∀ {β : Type tightening_u_1} {γ : Type tightening_u_2} [inst : DecidableEq γ]
  (F : Finset β) (f : β → γ) {g : ℕ},
  (∀ s ∈ Finset.image f F, {x ∈ F | f x = s}.card ≤ g) → F.card ≤ g * (Finset.image f F).card)
#guard_standard_axioms CoveringDesigns.BoundaryRank.card_le_mul_image_card
#print axioms CoveringDesigns.BoundaryRank.card_le_mul_image_card

#check (@CoveringDesigns.TwoKMinusTwoTightening.lower_bound_32_17_3 : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 32 → CoveringDesigns.IsCover C 17 3 → 13 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.lower_bound_32_17_3
#print axioms CoveringDesigns.TwoKMinusTwoTightening.lower_bound_32_17_3

#check (@CoveringDesigns.TwoKMinusTwoTightening.lower_bound_68_35_3 : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 68 → CoveringDesigns.IsCover C 35 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.lower_bound_68_35_3
#print axioms CoveringDesigns.TwoKMinusTwoTightening.lower_bound_68_35_3

#check (@CoveringDesigns.TwoKMinusTwoTightening.thirteen_le_card : ∀ {α : Type tightening_u_1} [inst : Fintype α] {k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 2 → 17 ≤ k → CoveringDesigns.IsCover C k 3 → 13 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.thirteen_le_card
#print axioms CoveringDesigns.TwoKMinusTwoTightening.thirteen_le_card

#check (@CoveringDesigns.TwoKMinusTwoTightening.fourteen_le_card : ∀ {α : Type tightening_u_1} [inst : Fintype α] {k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 2 → 35 ≤ k → CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.fourteen_le_card
#print axioms CoveringDesigns.TwoKMinusTwoTightening.fourteen_le_card

#check (@CoveringDesigns.TwoKMinusTwoTightening.exactness : ∀ {α : Type tightening_u_1} [inst : Fintype α] {k : ℕ},
  Fintype.card α = 2 * k - 2 →
    35 ≤ k →
      (∃ C, CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
        ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.exactness
#print axioms CoveringDesigns.TwoKMinusTwoTightening.exactness

#check (@CoveringDesigns.TwoKMinusTwoTightening.covering_number : ∀ {k : ℕ},
  35 ≤ k →
    (∃ C, CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family (Fin (2 * k - 2))), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.covering_number
#print axioms CoveringDesigns.TwoKMinusTwoTightening.covering_number

#check (@CoveringDesigns.TwoKMinusTwoTightening.interval_32_17_3_on : ∀ {α : Type tightening_u_1} [inst : Fintype α],
  Fintype.card α = 32 →
    (∃ C, CoveringDesigns.IsCover C 17 3 ∧ Finset.card C ≤ 14) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 17 3 → 13 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.interval_32_17_3_on
#print axioms CoveringDesigns.TwoKMinusTwoTightening.interval_32_17_3_on

#check (@CoveringDesigns.TwoKMinusTwoTightening.exactness_68_35_3_on : ∀ {α : Type tightening_u_1} [inst : Fintype α],
  Fintype.card α = 68 →
    (∃ C, CoveringDesigns.IsCover C 35 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 35 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.exactness_68_35_3_on
#print axioms CoveringDesigns.TwoKMinusTwoTightening.exactness_68_35_3_on

#check (@CoveringDesigns.TwoKMinusTwoTightening.low_completion : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.Uniform C k →
        12 ≤ Finset.card C →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
            (CoveringDesigns.BoundaryRank.centered (CoveringDesigns.TwoKMinusTwo.lowIncidence C) 6).rank =
                (CoveringDesigns.TwoKMinusTwo.lowIncidence C).rank ∧
              ((CoveringDesigns.BoundaryRank.centered (CoveringDesigns.TwoKMinusTwo.lowIncidence C) 6).mulVec fun x =>
                    1) =
                  0 ∧
                1 ≤ Finset.card C - (CoveringDesigns.TwoKMinusTwo.lowIncidence C).rank ∧
                  (CoveringDesigns.minimumPoints C 6).card +
                      CoveringDesigns.TwoKMinusTwoTightening.positiveDeficitCount C ≤
                    2 * (CoveringDesigns.TwoKMinusTwo.lowIncidence C).rank)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.low_completion
#print axioms CoveringDesigns.TwoKMinusTwoTightening.low_completion

#check (@CoveringDesigns.TwoKMinusTwoTightening.regularHigh_centered_image : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {y : α},
  y ∈ CoveringDesigns.TwoKMinusTwoTightening.regularHigh C →
    (CoveringDesigns.BoundaryRank.centered (CoveringDesigns.TwoKMinusTwo.lowIncidence C) 6).mulVec
        (CoveringDesigns.TwoKMinusTwoTightening.supportVector C y) =
      fun x => 3 - 6 / ↑(Fintype.card ↥C) * 7)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_centered_image
#print axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_centered_image

#check (@CoveringDesigns.TwoKMinusTwoTightening.regularHigh_supports_le_one : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α},
  ((CoveringDesigns.BoundaryRank.centered (CoveringDesigns.TwoKMinusTwo.lowIncidence C) 6).mulVec fun x => 1) = 0 →
    0 < Finset.card C →
      Finset.card C - (CoveringDesigns.BoundaryRank.centered (CoveringDesigns.TwoKMinusTwo.lowIncidence C) 6).rank ≤ 1 →
        (Finset.image (CoveringDesigns.TwoKMinusTwoTightening.supportVector C)
              (CoveringDesigns.TwoKMinusTwoTightening.regularHigh C)).card ≤
          1)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_supports_le_one
#print axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_supports_le_one

#check (@CoveringDesigns.TwoKMinusTwoTightening.regularHigh_supports_le_two : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α},
  ((CoveringDesigns.BoundaryRank.centered (CoveringDesigns.TwoKMinusTwo.lowIncidence C) 6).mulVec fun x => 1) = 0 →
    0 < Finset.card C →
      Finset.card C - (CoveringDesigns.BoundaryRank.centered (CoveringDesigns.TwoKMinusTwo.lowIncidence C) 6).rank ≤ 2 →
        (Finset.image (CoveringDesigns.TwoKMinusTwoTightening.supportVector C)
              (CoveringDesigns.TwoKMinusTwoTightening.regularHigh C)).card ≤
          2)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_supports_le_two
#print axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_supports_le_two

#check (@CoveringDesigns.TwoKMinusTwoTightening.regularHigh_card_le_five_mul : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α},
  Fintype.card α = 32 →
    CoveringDesigns.Uniform C 17 →
      (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
        (CoveringDesigns.TwoKMinusTwoTightening.regularHigh C).card ≤
          5 *
            (Finset.image (CoveringDesigns.TwoKMinusTwoTightening.supportVector C)
                (CoveringDesigns.TwoKMinusTwoTightening.regularHigh C)).card)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_card_le_five_mul
#print axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_card_le_five_mul

#check (@CoveringDesigns.TwoKMinusTwoTightening.regularHigh_card_le_ten_mul : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α},
  Fintype.card α = 68 →
    CoveringDesigns.Uniform C 35 →
      (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
        (CoveringDesigns.TwoKMinusTwoTightening.regularHigh C).card ≤
          10 *
            (Finset.image (CoveringDesigns.TwoKMinusTwoTightening.supportVector C)
                (CoveringDesigns.TwoKMinusTwoTightening.regularHigh C)).card)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_card_le_ten_mul
#print axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_card_le_ten_mul

#check (@CoveringDesigns.TwoKMinusTwoTightening.no_twelve_32_17 : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 32 →
    CoveringDesigns.Uniform C 17 →
      Finset.card C = 12 →
        (∀ (x : α), 6 ≤ CoveringDesigns.degree C x) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) → False)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.no_twelve_32_17
#print axioms CoveringDesigns.TwoKMinusTwoTightening.no_twelve_32_17

#check (@CoveringDesigns.TwoKMinusTwoTightening.no_thirteen_68_35 : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 68 →
    CoveringDesigns.Uniform C 35 →
      Finset.card C = 13 →
        (∀ (x : α), 6 ≤ CoveringDesigns.degree C x) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) → False)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.no_thirteen_68_35
#print axioms CoveringDesigns.TwoKMinusTwoTightening.no_thirteen_68_35

#check (@CoveringDesigns.TwoKMinusTwoTightening.regularHigh_degree : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {y : α},
  y ∈ CoveringDesigns.TwoKMinusTwoTightening.regularHigh C → CoveringDesigns.degree C y = 7)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_degree
#print axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_degree

#check (@CoveringDesigns.TwoKMinusTwoTightening.regularHigh_pair : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {y : α},
  y ∈ CoveringDesigns.TwoKMinusTwoTightening.regularHigh C →
    ∀ (x : CoveringDesigns.TwoKMinusTwo.Low C), CoveringDesigns.degree (CoveringDesigns.star C ↑x) y = 3)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_pair
#print axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_pair

#check (@CoveringDesigns.TwoKMinusTwoTightening.supportVector_binary : ∀ {α : Type tightening_u_1} [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (y : α) (B : ↥C),
  CoveringDesigns.TwoKMinusTwoTightening.supportVector C y B = 0 ∨
    CoveringDesigns.TwoKMinusTwoTightening.supportVector C y B = 1)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.supportVector_binary
#print axioms CoveringDesigns.TwoKMinusTwoTightening.supportVector_binary

#check (@CoveringDesigns.TwoKMinusTwoTightening.supportVector_sum : ∀ {α : Type tightening_u_1} [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (y : α),
  ∑ B, CoveringDesigns.TwoKMinusTwoTightening.supportVector C y B = ↑(CoveringDesigns.degree C y))
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.supportVector_sum
#print axioms CoveringDesigns.TwoKMinusTwoTightening.supportVector_sum

#check (@CoveringDesigns.TwoKMinusTwoTightening.supportVector_eq_iff : ∀ {α : Type tightening_u_1} [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (x y : α),
  CoveringDesigns.TwoKMinusTwoTightening.supportVector C x = CoveringDesigns.TwoKMinusTwoTightening.supportVector C y ↔
    ∀ B ∈ C, x ∈ B ↔ y ∈ B)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.supportVector_eq_iff
#print axioms CoveringDesigns.TwoKMinusTwoTightening.supportVector_eq_iff

#check (@CoveringDesigns.TwoKMinusTwoTightening.low_row_sum : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (C : CoveringDesigns.Family α) (x : CoveringDesigns.TwoKMinusTwo.Low C),
  ∑ B, CoveringDesigns.TwoKMinusTwo.lowIncidence C x B = 6)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.low_row_sum
#print axioms CoveringDesigns.TwoKMinusTwoTightening.low_row_sum

#check (@CoveringDesigns.TwoKMinusTwoTightening.supportVector_image : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] (C : CoveringDesigns.Family α) (y : α),
  (CoveringDesigns.TwoKMinusTwo.lowIncidence C).mulVec (CoveringDesigns.TwoKMinusTwoTightening.supportVector C y) =
    fun x => ↑(CoveringDesigns.degree (CoveringDesigns.star C ↑x) y))
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.supportVector_image
#print axioms CoveringDesigns.TwoKMinusTwoTightening.supportVector_image

#check (@CoveringDesigns.TwoKMinusTwoTightening.high_image : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {y : α},
  y ∈ CoveringDesigns.TwoKMinusTwoTightening.regularHigh C →
    (CoveringDesigns.TwoKMinusTwo.lowIncidence C).mulVec (CoveringDesigns.TwoKMinusTwoTightening.supportVector C y) =
      fun x => 3)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.high_image
#print axioms CoveringDesigns.TwoKMinusTwoTightening.high_image

#check (@CoveringDesigns.TwoKMinusTwoTightening.low_total_excess : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.Uniform C k →
        ∀ (x : CoveringDesigns.TwoKMinusTwo.Low C), ∑ y, CoveringDesigns.TwoKMinusTwo.excess C (↑x) y = 3)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.low_total_excess
#print axioms CoveringDesigns.TwoKMinusTwoTightening.low_total_excess

#check (@CoveringDesigns.TwoKMinusTwoTightening.deficit_eq_high_sum : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.Uniform C k →
        ∀ (x : CoveringDesigns.TwoKMinusTwo.Low C),
          CoveringDesigns.TwoKMinusTwo.deficit C x =
            ∑ y ∈ Finset.univ \ CoveringDesigns.minimumPoints C 6, CoveringDesigns.TwoKMinusTwo.excess C (↑x) y)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.deficit_eq_high_sum
#print axioms CoveringDesigns.TwoKMinusTwoTightening.deficit_eq_high_sum

#check (@CoveringDesigns.TwoKMinusTwoTightening.deficit_sum_le : ∀ {α : Type tightening_u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.Uniform C k →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
          ∑ x, CoveringDesigns.TwoKMinusTwo.deficit C x ≤
            3 * ↑(CoveringDesigns.TwoKMinusTwoTightening.positiveDeficitCount C))
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.deficit_sum_le
#print axioms CoveringDesigns.TwoKMinusTwoTightening.deficit_sum_le

#check (@CoveringDesigns.TwoKMinusTwoTightening.regularHigh_count_bound : ∀ {α : Type tightening_u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.Uniform C k →
        (∀ (y : α), 6 ≤ CoveringDesigns.degree C y) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
            8 * Fintype.card α ≤
              k * Finset.card C + 2 * (CoveringDesigns.minimumPoints C 6).card +
                  3 * CoveringDesigns.TwoKMinusTwoTightening.positiveDeficitCount C +
                (CoveringDesigns.TwoKMinusTwoTightening.regularHigh C).card)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_count_bound
#print axioms CoveringDesigns.TwoKMinusTwoTightening.regularHigh_count_bound

#check (@CoveringDesigns.TwoKMinusTwoTightening.mem_regularHigh_iff :
  ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : CoveringDesigns.Family α} {y : α},
    y ∈ CoveringDesigns.TwoKMinusTwoTightening.regularHigh C ↔
    CoveringDesigns.degree C y = 7 ∧
      ∀ x : CoveringDesigns.TwoKMinusTwo.Low C, CoveringDesigns.degree (CoveringDesigns.star C x.val) y = 3)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.mem_regularHigh_iff
#print axioms CoveringDesigns.TwoKMinusTwoTightening.mem_regularHigh_iff

namespace CoveringDesigns.AuditTwoKMinusTwoTightening

theorem exactness_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α=2*k-2) (hk : 35≤k) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card=k) ∧
      (∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) ∧ C.card=14) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card=k) →
      (∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) → 14≤C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hlower⟩ := TwoKMinusTwoTightening.exactness hv hk
  exact ⟨⟨C,hC.1,hC.2,hcard⟩, fun C hu hc => hlower C ⟨hu,hc⟩⟩

theorem lower_thirteen_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α=2*k-2) (hk : 17≤k)
    (C : Finset (Finset α)) (hu : ∀ B ∈ C, B.card=k)
    (hc : ∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) : 13≤C.card :=
  TwoKMinusTwoTightening.thirteen_le_card hv hk ⟨hu,hc⟩

end CoveringDesigns.AuditTwoKMinusTwoTightening
#guard_standard_axioms CoveringDesigns.AuditTwoKMinusTwoTightening.exactness_explicit
  CoveringDesigns.AuditTwoKMinusTwoTightening.lower_thirteen_explicit
#print axioms CoveringDesigns.AuditTwoKMinusTwoTightening.exactness_explicit
#print axioms CoveringDesigns.AuditTwoKMinusTwoTightening.lower_thirteen_explicit

end TighteningContracts
