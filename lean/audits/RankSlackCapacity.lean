import CoveringDesigns.RankSlackCapacity

/-! Full public contracts, definition inspection and transitive axiom checks.
All 64 new public theorems are typed below. Explicit restatements at the end
expand both indexed pair multiplicity and ordinary coverage. -/
section CapacityContracts
attribute [local instance] Classical.propDecidable
open Finset Matrix
open scoped BigOperators
set_option linter.unusedVariables false
universe u_1 u_2 u_3

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.indexedDegree
#print CoveringDesigns.indexedSubsetDegree
#print CoveringDesigns.AffineCapacity.dimension
#print CoveringDesigns.AffineCapacity.row
#print CoveringDesigns.SupportDimension.coordinateSum
#print CoveringDesigns.SupportDimension.zeroSumKernel
#print CoveringDesigns.BoundaryIncidence.lowPoints
#print CoveringDesigns.BoundaryIncidence.Low
#print CoveringDesigns.BoundaryIncidence.highPoints
#print CoveringDesigns.BoundaryIncidence.excess
#print CoveringDesigns.BoundaryIncidence.deficit
#print CoveringDesigns.BoundaryIncidence.positiveCount
#print CoveringDesigns.BoundaryIncidence.eta
#print CoveringDesigns.BoundaryIncidence.regularPoints
#print CoveringDesigns.BoundaryIncidence.incidence
#print CoveringDesigns.BoundaryIncidence.excessMatrix
#print CoveringDesigns.BoundaryIncidence.lowerCount

#check (@CoveringDesigns.AffineCapacity.exists_spanning_points : ∀ {α : Type u_1} {ι : Type u_2} [Fintype ι] (F : Finset α),
  F.Nonempty →
    ∀ (w : α → ι → ℝ),
      ∃ S ⊆ F,
        S.card = CoveringDesigns.AffineCapacity.dimension (w '' (↑F : Set α)) + 1 ∧
          affineSpan ℝ (w '' (↑S : Set α)) = affineSpan ℝ (w '' (↑F : Set α)))
#guard_standard_axioms CoveringDesigns.AffineCapacity.exists_spanning_points
#print axioms CoveringDesigns.AffineCapacity.exists_spanning_points

#check (@CoveringDesigns.AffineCapacity.coordinate_eq_of_mem_affineSpan : ∀ {ι : Type u_1} {s : Set (ι → ℝ)} {z : ι → ℝ},
  z ∈ affineSpan ℝ s → ∀ (i : ι) (c : ℝ), (∀ w ∈ s, w i = c) → z i = c)
#guard_standard_axioms CoveringDesigns.AffineCapacity.coordinate_eq_of_mem_affineSpan
#print axioms CoveringDesigns.AffineCapacity.coordinate_eq_of_mem_affineSpan

#check (@CoveringDesigns.AffineCapacity.row_eq_one_iff : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  (B : ι → Finset α) (x : α) (i : ι), CoveringDesigns.AffineCapacity.row B x i = 1 ↔ x ∈ B i)
#guard_standard_axioms CoveringDesigns.AffineCapacity.row_eq_one_iff
#print axioms CoveringDesigns.AffineCapacity.row_eq_one_iff

#check (@CoveringDesigns.AffineCapacity.common_support_eq : ∀ {α : Type u_1} {ι : Type u_2} [Fintype ι] [inst : DecidableEq α]
  (B : ι → Finset α) (F S : Finset α),
  S ⊆ F →
    affineSpan ℝ (CoveringDesigns.AffineCapacity.row B '' (↑S : Set α)) =
        affineSpan ℝ (CoveringDesigns.AffineCapacity.row B '' (↑F : Set α)) →
      {i | ∀ x ∈ F, x ∈ B i} = {i | ∀ x ∈ S, x ∈ B i})
#guard_standard_axioms CoveringDesigns.AffineCapacity.common_support_eq
#print axioms CoveringDesigns.AffineCapacity.common_support_eq

#check (@CoveringDesigns.AffineCapacity.exists_block_of_dimension_lt : ∀ {α : Type u_1} {ι : Type u_2} [Fintype ι]
  [inst : Fintype α] [inst_1 : DecidableEq α] (B : ι → Finset α) (F : Finset α) {t : ℕ},
  F.Nonempty →
    1 ≤ t →
      t ≤ Fintype.card α →
        (∀ (U : Finset α), U.card = t → ∃ i, U ⊆ B i) →
          CoveringDesigns.AffineCapacity.dimension (CoveringDesigns.AffineCapacity.row B '' (↑F : Set α)) < t →
            ∃ i, F ⊆ B i)
#guard_standard_axioms CoveringDesigns.AffineCapacity.exists_block_of_dimension_lt
#print axioms CoveringDesigns.AffineCapacity.exists_block_of_dimension_lt

#check (@CoveringDesigns.AffineCapacity.card_le_of_dimension_lt : ∀ {α : Type u_1} {ι : Type u_2} [Fintype ι] [inst : Fintype α]
  [inst_1 : DecidableEq α] (B : ι → Finset α) (F : Finset α) {t k : ℕ},
  1 ≤ t →
    t ≤ Fintype.card α →
      (∀ (U : Finset α), U.card = t → ∃ i, U ⊆ B i) →
        (∀ (i : ι), (B i).card ≤ k) →
          CoveringDesigns.AffineCapacity.dimension (CoveringDesigns.AffineCapacity.row B '' (↑F : Set α)) < t →
            F.card ≤ k)
#guard_standard_axioms CoveringDesigns.AffineCapacity.card_le_of_dimension_lt
#print axioms CoveringDesigns.AffineCapacity.card_le_of_dimension_lt

#check (@CoveringDesigns.AffineCapacity.binary_card_le_pow : ∀ {ι : Type u_1} [Fintype ι] (W : Submodule ℝ (ι → ℝ))
  (S : Finset (ι → ℝ)),
  (∀ x ∈ S, ∀ (i : ι), x i = 0 ∨ x i = 1) → (∀ x ∈ S, ∀ y ∈ S, x - y ∈ W) → S.card ≤ 2 ^ Module.finrank ℝ ↥W)
#guard_standard_axioms CoveringDesigns.AffineCapacity.binary_card_le_pow
#print axioms CoveringDesigns.AffineCapacity.binary_card_le_pow

#check (@CoveringDesigns.AffineCapacity.binary_affine_card_le_pow : ∀ {ι : Type u_1} [Fintype ι] (A : AffineSubspace ℝ (ι → ℝ))
  (S : Finset (ι → ℝ)),
  (↑S : Set (ι → ℝ)) ⊆ (↑A : Set (ι → ℝ)) →
    (∀ x ∈ S, ∀ (i : ι), x i = 0 ∨ x i = 1) → S.card ≤ 2 ^ Module.finrank ℝ ↥A.direction)
#guard_standard_axioms CoveringDesigns.AffineCapacity.binary_affine_card_le_pow
#print axioms CoveringDesigns.AffineCapacity.binary_affine_card_le_pow

#check (@CoveringDesigns.SupportDimension.one_le_corank : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι] [inst : Fintype κ]
  (T : Matrix ι κ ℝ), 0 < Fintype.card κ → (T.mulVec fun x => 1) = 0 → 1 ≤ Fintype.card κ - T.rank)
#guard_standard_axioms CoveringDesigns.SupportDimension.one_le_corank
#print axioms CoveringDesigns.SupportDimension.one_le_corank

#check (@CoveringDesigns.SupportDimension.zeroSumKernel_finrank : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι] [inst : Fintype κ]
  (T : Matrix ι κ ℝ),
  0 < Fintype.card κ →
    (T.mulVec fun x => 1) = 0 →
      Module.finrank ℝ ↥(CoveringDesigns.SupportDimension.zeroSumKernel T) = Fintype.card κ - T.rank - 1)
#guard_standard_axioms CoveringDesigns.SupportDimension.zeroSumKernel_finrank
#print axioms CoveringDesigns.SupportDimension.zeroSumKernel_finrank

#check (@CoveringDesigns.SupportDimension.sub_mem_zeroSumKernel : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι] [inst : Fintype κ]
  (T : Matrix ι κ ℝ) {x y : κ → ℝ},
  T.mulVec x = T.mulVec y → ∑ i, x i = ∑ i, y i → x - y ∈ CoveringDesigns.SupportDimension.zeroSumKernel T)
#guard_standard_axioms CoveringDesigns.SupportDimension.sub_mem_zeroSumKernel
#print axioms CoveringDesigns.SupportDimension.sub_mem_zeroSumKernel

#check (@CoveringDesigns.SupportDimension.fibre_eq_translate : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι] [inst : Fintype κ]
  (T : Matrix ι κ ℝ) (a : ι → ℝ) (h : ℝ) (w₀ : κ → ℝ),
  T.mulVec w₀ = a →
    ∑ i, w₀ i = h →
      {w | T.mulVec w = a ∧ ∑ i, w i = h} =
        (↑(AffineSubspace.mk' w₀ (CoveringDesigns.SupportDimension.zeroSumKernel T)) : Set (κ → ℝ)))
#guard_standard_axioms CoveringDesigns.SupportDimension.fibre_eq_translate
#print axioms CoveringDesigns.SupportDimension.fibre_eq_translate

#check (@CoveringDesigns.SupportDimension.fibre_dimension : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι] [inst : Fintype κ]
  (T : Matrix ι κ ℝ),
  0 < Fintype.card κ →
    (T.mulVec fun x => 1) = 0 →
      ∀ (a : ι → ℝ) (h : ℝ) (w₀ : κ → ℝ),
        T.mulVec w₀ = a →
          ∑ i, w₀ i = h →
            CoveringDesigns.AffineCapacity.dimension {w | T.mulVec w = a ∧ ∑ i, w i = h} = Fintype.card κ - T.rank - 1)
#guard_standard_axioms CoveringDesigns.SupportDimension.fibre_dimension
#print axioms CoveringDesigns.SupportDimension.fibre_dimension

#check (@CoveringDesigns.SupportDimension.family_dimension_le : ∀ {ι : Type u_1} {κ : Type u_2} {α : Type u_3} [Fintype ι]
  [inst : Fintype κ] (T : Matrix ι κ ℝ),
  0 < Fintype.card κ →
    (T.mulVec fun x => 1) = 0 →
      ∀ (F : Finset α) (w : α → κ → ℝ) (a : ι → ℝ) (h : ℝ),
        (∀ x ∈ F, T.mulVec (w x) = a) →
          (∀ x ∈ F, ∑ i, w x i = h) →
            CoveringDesigns.AffineCapacity.dimension (w '' (↑F : Set α)) ≤ Fintype.card κ - T.rank - 1)
#guard_standard_axioms CoveringDesigns.SupportDimension.family_dimension_le
#print axioms CoveringDesigns.SupportDimension.family_dimension_le

#check (@CoveringDesigns.SupportDimension.binary_support_card_le : ∀ {ι : Type u_1} {κ : Type u_2} {α : Type u_3} [Fintype ι]
  [inst : Fintype κ] (T : Matrix ι κ ℝ),
  0 < Fintype.card κ →
    (T.mulVec fun x => 1) = 0 →
      ∀ (F : Finset α) (w : α → κ → ℝ),
        (∀ x ∈ F, ∀ (i : κ), w x i = 0 ∨ w x i = 1) →
          ∀ (a : ι → ℝ) (h : ℝ),
            (∀ x ∈ F, T.mulVec (w x) = a) →
              (∀ x ∈ F, ∑ i, w x i = h) → (Finset.image w F).card ≤ 2 ^ (Fintype.card κ - T.rank - 1))
#guard_standard_axioms CoveringDesigns.SupportDimension.binary_support_card_le
#print axioms CoveringDesigns.SupportDimension.binary_support_card_le

#check (@CoveringDesigns.SupportDimension.common_block : ∀ {ι : Type u_1} {κ : Type u_2} {α : Type u_3} [Fintype ι]
  [inst : Fintype κ] [inst_1 : Fintype α] [inst_2 : DecidableEq α] (B : κ → Finset α) (F : Finset α),
  F.Nonempty →
    ∀ (T : Matrix ι κ ℝ),
      0 < Fintype.card κ →
        (T.mulVec fun x => 1) = 0 →
          ∀ {t : ℕ},
            1 ≤ t →
              t ≤ Fintype.card α →
                (∀ (U : Finset α), U.card = t → ∃ i, U ⊆ B i) →
                  Fintype.card κ - T.rank ≤ t →
                    ∀ (a : ι → ℝ) (h : ℝ),
                      (∀ x ∈ F, T.mulVec (CoveringDesigns.AffineCapacity.row B x) = a) →
                        (∀ x ∈ F, ∑ i, CoveringDesigns.AffineCapacity.row B x i = h) → ∃ i, F ⊆ B i)
#guard_standard_axioms CoveringDesigns.SupportDimension.common_block
#print axioms CoveringDesigns.SupportDimension.common_block

#check (@CoveringDesigns.SupportCapacity.aggregate : ∀ {α : Type u_1} {ι : Type u_2} {β : Type u_3} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] [inst_3 : DecidableEq β] (B : ι → Finset α) (F : Finset α) (f : α → β)
  {k h lam : ℕ},
  (∀ (i : ι), (B i).card = k) →
    (∀ x ∈ F, CoveringDesigns.indexedDegree B x = h) →
      (∀ x ∈ F, ∀ y ∈ F, f x = f y → ∀ (i : ι), x ∈ B i ↔ y ∈ B i) →
        (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          lam * Fintype.card α * (Finset.image f F).card + h * F.card ≤ h * k * (Finset.image f F).card + lam * F.card)
#guard_standard_axioms CoveringDesigns.SupportCapacity.aggregate
#print axioms CoveringDesigns.SupportCapacity.aggregate

#check (@CoveringDesigns.SupportCapacity.signed_aggregate : ∀ {α : Type u_1} {ι : Type u_2} {β : Type u_3} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] [inst_3 : DecidableEq β] (B : ι → Finset α) (F : Finset α) (f : α → β)
  {k h lam : ℕ},
  (∀ (i : ι), (B i).card = k) →
    (∀ x ∈ F, CoveringDesigns.indexedDegree B x = h) →
      (∀ x ∈ F, ∀ y ∈ F, f x = f y → ∀ (i : ι), x ∈ B i ↔ y ∈ B i) →
        (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          ((↑h : ℝ) - (↑lam : ℝ)) * (↑F.card : ℝ) ≤
            (↑(Finset.image f F).card : ℝ) * ((↑h : ℝ) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ)))
#guard_standard_axioms CoveringDesigns.SupportCapacity.signed_aggregate
#print axioms CoveringDesigns.SupportCapacity.signed_aggregate

#check (@CoveringDesigns.SupportCapacity.of_support_bound : ∀ {α : Type u_1} {ι : Type u_2} {β : Type u_3} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] [inst_3 : DecidableEq β] (B : ι → Finset α) (F : Finset α) (f : α → β)
  {k h lam M : ℕ},
  (∀ (i : ι), (B i).card = k) →
    (∀ x ∈ F, CoveringDesigns.indexedDegree B x = h) →
      (∀ x ∈ F, ∀ y ∈ F, f x = f y → ∀ (i : ι), x ∈ B i ↔ y ∈ B i) →
        (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          (Finset.image f F).card ≤ M →
            0 ≤ (↑h : ℝ) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ) →
              ((↑h : ℝ) - (↑lam : ℝ)) * (↑F.card : ℝ) ≤
                (↑M : ℝ) * ((↑h : ℝ) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ)))
#guard_standard_axioms CoveringDesigns.SupportCapacity.of_support_bound
#print axioms CoveringDesigns.SupportCapacity.of_support_bound

#check (@CoveringDesigns.SupportCapacity.numerator_pos : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) (F : Finset α) {k h lam : ℕ},
  (∀ (i : ι), (B i).card = k) →
    F.Nonempty →
      (∀ x ∈ F, CoveringDesigns.indexedDegree B x = h) →
        (∀ x ∈ F, ∀ y ∈ F, ∀ (i : ι), x ∈ B i ↔ y ∈ B i) →
          (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
            lam < h → (↑h : ℝ) - (↑lam : ℝ) ≤ (↑h : ℝ) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ))
#guard_standard_axioms CoveringDesigns.SupportCapacity.numerator_pos
#print axioms CoveringDesigns.SupportCapacity.numerator_pos

#check (@CoveringDesigns.SupportCapacity.card_le_div_of_support_bound : ∀ {α : Type u_1} {ι : Type u_2} {β : Type u_3}
  [inst : Fintype α] [inst_1 : Fintype ι] [inst_2 : DecidableEq α] [inst_3 : DecidableEq β] (B : ι → Finset α)
  (F : Finset α) (f : α → β) {k h lam M : ℕ},
  (∀ (i : ι), (B i).card = k) →
    (∀ x ∈ F, CoveringDesigns.indexedDegree B x = h) →
      (∀ x ∈ F, ∀ y ∈ F, f x = f y → ∀ (i : ι), x ∈ B i ↔ y ∈ B i) →
        (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          (Finset.image f F).card ≤ M →
            lam < h →
              0 ≤ (↑h : ℝ) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ) →
                (↑F.card : ℝ) ≤
                  (↑M : ℝ) * ((↑h : ℝ) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ)) / ((↑h : ℝ) - (↑lam : ℝ)))
#guard_standard_axioms CoveringDesigns.SupportCapacity.card_le_div_of_support_bound
#print axioms CoveringDesigns.SupportCapacity.card_le_div_of_support_bound

#check (@CoveringDesigns.DeficitCharging.bad_card_le : ∀ {α : Type u_1} {β : Type u_2} (H : Finset α) (L : Finset β)
  (degreeExcess : α → ℕ) (imageExcess : β → α → ℕ),
  {y ∈ H | ¬(degreeExcess y = 0 ∧ ∀ x ∈ L, imageExcess x y = 0)}.card ≤
    ∑ y ∈ H, degreeExcess y + ∑ x ∈ L, ∑ y ∈ H, imageExcess x y)
#guard_standard_axioms CoveringDesigns.DeficitCharging.bad_card_le
#print axioms CoveringDesigns.DeficitCharging.bad_card_le

#check (@CoveringDesigns.DeficitCharging.sum_le_mul_positive : ∀ {β : Type u_1} (L : Finset β) (δ : β → ℕ) (D : ℕ),
  (∀ x ∈ L, δ x ≤ D) → ∑ x ∈ L, δ x ≤ D * {x ∈ L | 0 < δ x}.card)
#guard_standard_axioms CoveringDesigns.DeficitCharging.sum_le_mul_positive
#print axioms CoveringDesigns.DeficitCharging.sum_le_mul_positive

#check (@CoveringDesigns.DeficitCharging.regular_count : ∀ {α : Type u_1} {β : Type u_2} (H : Finset α) (L : Finset β)
  (degreeExcess : α → ℕ) (imageExcess : β → α → ℕ) (D : ℕ),
  (∀ x ∈ L, ∑ y ∈ H, imageExcess x y ≤ D) →
    H.card ≤
      {y ∈ H | degreeExcess y = 0 ∧ ∀ x ∈ L, imageExcess x y = 0}.card + ∑ y ∈ H, degreeExcess y +
        D * {x ∈ L | 0 < ∑ y ∈ H, imageExcess x y}.card)
#guard_standard_axioms CoveringDesigns.DeficitCharging.regular_count
#print axioms CoveringDesigns.DeficitCharging.regular_count

#check (@CoveringDesigns.BoundaryIncidence.low_degree : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) (r : ℕ) (x : CoveringDesigns.BoundaryIncidence.Low B r),
  CoveringDesigns.indexedDegree B (↑x : α) = r)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.low_degree
#print axioms CoveringDesigns.BoundaryIncidence.low_degree

#check (@CoveringDesigns.BoundaryIncidence.high_degree : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) (r : ℕ),
  (∀ (x : α), r ≤ CoveringDesigns.indexedDegree B x) →
    ∀ {y : α}, y ∈ CoveringDesigns.BoundaryIncidence.highPoints B r → r + 1 ≤ CoveringDesigns.indexedDegree B y)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.high_degree
#print axioms CoveringDesigns.BoundaryIncidence.high_degree

#check (@CoveringDesigns.BoundaryIncidence.low_ne_high : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) (r : ℕ) (x : CoveringDesigns.BoundaryIncidence.Low B r) {y : α},
  y ∈ CoveringDesigns.BoundaryIncidence.highPoints B r → (↑x : α) ≠ y)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.low_ne_high
#print axioms CoveringDesigns.BoundaryIncidence.low_ne_high

#check (@CoveringDesigns.BoundaryIncidence.pair_self : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : Fintype ι]
  [inst_1 : DecidableEq α] (B : ι → Finset α) (x : α),
  CoveringDesigns.indexedSubsetDegree B {x, x} = CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.pair_self
#print axioms CoveringDesigns.BoundaryIncidence.pair_self

#check (@CoveringDesigns.BoundaryIncidence.singleton_degree : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : Fintype ι]
  [inst_1 : DecidableEq α] (B : ι → Finset α) (x : α),
  CoveringDesigns.indexedSubsetDegree B {x} = CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.singleton_degree
#print axioms CoveringDesigns.BoundaryIncidence.singleton_degree

#check (@CoveringDesigns.BoundaryIncidence.pair_comm : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : Fintype ι]
  [inst_1 : DecidableEq α] (B : ι → Finset α) (x y : α),
  CoveringDesigns.indexedSubsetDegree B {x, y} = CoveringDesigns.indexedSubsetDegree B {y, x})
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.pair_comm
#print axioms CoveringDesigns.BoundaryIncidence.pair_comm

#check (@CoveringDesigns.BoundaryIncidence.row_binary : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [Fintype ι]
  [inst : DecidableEq α] (B : ι → Finset α) (x : α) (i : ι),
  CoveringDesigns.AffineCapacity.row B x i = 0 ∨ CoveringDesigns.AffineCapacity.row B x i = 1)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.row_binary
#print axioms CoveringDesigns.BoundaryIncidence.row_binary

#check (@CoveringDesigns.BoundaryIncidence.row_sum : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : Fintype ι]
  [inst_1 : DecidableEq α] (B : ι → Finset α) (x : α),
  ∑ i, CoveringDesigns.AffineCapacity.row B x i = (↑(CoveringDesigns.indexedDegree B x) : ℝ))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.row_sum
#print axioms CoveringDesigns.BoundaryIncidence.row_sum

#check (@CoveringDesigns.BoundaryIncidence.row_dot : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : Fintype ι]
  [inst_1 : DecidableEq α] (B : ι → Finset α) (x y : α),
  ∑ i, CoveringDesigns.AffineCapacity.row B x i * CoveringDesigns.AffineCapacity.row B y i =
    (↑(CoveringDesigns.indexedSubsetDegree B {x, y}) : ℝ))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.row_dot
#print axioms CoveringDesigns.BoundaryIncidence.row_dot

#check (@CoveringDesigns.BoundaryIncidence.degree_sum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) {k : ℕ},
  (∀ (i : ι), (B i).card = k) → ∑ x, CoveringDesigns.indexedDegree B x = k * Fintype.card ι)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.degree_sum
#print axioms CoveringDesigns.BoundaryIncidence.degree_sum

#check (@CoveringDesigns.BoundaryIncidence.excess_cast : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : Fintype ι]
  [inst_1 : DecidableEq α] (B : ι → Finset α) (lam : ℕ),
  (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
    ∀ (x y : α),
      (↑(CoveringDesigns.BoundaryIncidence.excess B lam x y) : ℝ) =
        (↑(CoveringDesigns.indexedSubsetDegree B {x, y}) : ℝ) - (↑lam : ℝ) -
          if x = y then (↑(CoveringDesigns.indexedDegree B x) : ℝ) - (↑lam : ℝ) else 0)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.excess_cast
#print axioms CoveringDesigns.BoundaryIncidence.excess_cast

#check (@CoveringDesigns.BoundaryIncidence.total_excess : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  (∀ (i : ι), (B i).card = k) →
    (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
      (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
        ∀ (x : CoveringDesigns.BoundaryIncidence.Low B r),
          ∑ y, (↑(CoveringDesigns.BoundaryIncidence.excess B lam (↑x : α) y) : ℝ) = (↑r : ℝ) - (↑lam : ℝ))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.total_excess
#print axioms CoveringDesigns.BoundaryIncidence.total_excess

#check (@CoveringDesigns.BoundaryIncidence.balance : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  (∀ (i : ι), (B i).card = k) →
    (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
      (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
        ∀ (x : CoveringDesigns.BoundaryIncidence.Low B r),
          ∑ y, CoveringDesigns.BoundaryIncidence.excessMatrix B r lam x y +
              (↑(CoveringDesigns.BoundaryIncidence.deficit B r lam x) : ℝ) =
            (↑r : ℝ) - (↑lam : ℝ))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.balance
#print axioms CoveringDesigns.BoundaryIncidence.balance

#check (@CoveringDesigns.BoundaryIncidence.gram : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) {r lam : ℕ},
  (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
    CoveringDesigns.BoundaryIncidence.incidence B r * (CoveringDesigns.BoundaryIncidence.incidence B r).transpose =
      (Matrix.diagonal fun x => (↑r : ℝ) - (↑lam : ℝ)) + CoveringDesigns.BoundaryIncidence.excessMatrix B r lam +
        (Matrix.of :
            (CoveringDesigns.BoundaryIncidence.Low B r → CoveringDesigns.BoundaryIncidence.Low B r → ℝ) →
              Matrix (CoveringDesigns.BoundaryIncidence.Low B r) (CoveringDesigns.BoundaryIncidence.Low B r) ℝ)
          fun x x_1 => (↑lam : ℝ))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.gram
#print axioms CoveringDesigns.BoundaryIncidence.gram

#check (@CoveringDesigns.BoundaryIncidence.completion : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  0 < Fintype.card ι →
    lam < r →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
            (↑r : ℝ) ^ 2 ≤ (↑(Fintype.card ι) : ℝ) * (↑lam : ℝ) →
              (CoveringDesigns.BoundaryRank.centered (CoveringDesigns.BoundaryIncidence.incidence B r) (↑r : ℝ)).rank =
                  (CoveringDesigns.BoundaryIncidence.incidence B r).rank ∧
                ((CoveringDesigns.BoundaryRank.centered (CoveringDesigns.BoundaryIncidence.incidence B r)
                          (↑r : ℝ)).mulVec
                      fun x => 1) =
                    0 ∧
                  1 ≤ Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank ∧
                    (CoveringDesigns.BoundaryIncidence.lowPoints B r).card +
                        CoveringDesigns.BoundaryIncidence.positiveCount B r lam ≤
                      2 * (CoveringDesigns.BoundaryIncidence.incidence B r).rank)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.completion
#print axioms CoveringDesigns.BoundaryIncidence.completion

#check (@CoveringDesigns.BoundaryIncidence.degree_balance : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) {k r : ℕ},
  (∀ (i : ι), (B i).card = k) →
    (∀ (x : α), r ≤ CoveringDesigns.indexedDegree B x) →
      k * Fintype.card ι + (CoveringDesigns.BoundaryIncidence.lowPoints B r).card =
        (r + 1) * Fintype.card α + CoveringDesigns.BoundaryIncidence.eta B r)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.degree_balance
#print axioms CoveringDesigns.BoundaryIncidence.degree_balance

#check (@CoveringDesigns.BoundaryIncidence.regular_degree : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) (r lam : ℕ) {y : α},
  y ∈ CoveringDesigns.BoundaryIncidence.regularPoints B r lam → CoveringDesigns.indexedDegree B y = r + 1)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.regular_degree
#print axioms CoveringDesigns.BoundaryIncidence.regular_degree

#check (@CoveringDesigns.BoundaryIncidence.regular_image : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) (r lam : ℕ) {y : α},
  y ∈ CoveringDesigns.BoundaryIncidence.regularPoints B r lam →
    (CoveringDesigns.BoundaryIncidence.incidence B r).mulVec (CoveringDesigns.AffineCapacity.row B y) = fun x =>
      (↑lam : ℝ))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.regular_image
#print axioms CoveringDesigns.BoundaryIncidence.regular_image

#check (@CoveringDesigns.BoundaryIncidence.regular_centered_image : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) (r lam : ℕ) {y : α},
  y ∈ CoveringDesigns.BoundaryIncidence.regularPoints B r lam →
    (CoveringDesigns.BoundaryRank.centered (CoveringDesigns.BoundaryIncidence.incidence B r) (↑r : ℝ)).mulVec
        (CoveringDesigns.AffineCapacity.row B y) =
      fun x => (↑lam : ℝ) - (↑r : ℝ) / (↑(Fintype.card ι) : ℝ) * ((↑r : ℝ) + 1))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.regular_centered_image
#print axioms CoveringDesigns.BoundaryIncidence.regular_centered_image

#check (@CoveringDesigns.BoundaryIncidence.deficit_le : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  lam < r →
    (∀ (i : ι), (B i).card = k) →
      (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
        (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
          ∀ (x : CoveringDesigns.BoundaryIncidence.Low B r),
            CoveringDesigns.BoundaryIncidence.deficit B r lam x ≤ r - lam)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.deficit_le
#print axioms CoveringDesigns.BoundaryIncidence.deficit_le

#check (@CoveringDesigns.BoundaryIncidence.regular_count : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  lam < r →
    (∀ (i : ι), (B i).card = k) →
      (∀ (x : α), r ≤ CoveringDesigns.indexedDegree B x) →
        (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
            (CoveringDesigns.BoundaryIncidence.highPoints B r).card ≤
              (CoveringDesigns.BoundaryIncidence.regularPoints B r lam).card +
                  CoveringDesigns.BoundaryIncidence.eta B r +
                (r - lam) * CoveringDesigns.BoundaryIncidence.positiveCount B r lam)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.regular_count
#print axioms CoveringDesigns.BoundaryIncidence.regular_count

#check (@CoveringDesigns.BoundaryIncidence.lowerCount_le : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  0 < Fintype.card ι →
    lam < r →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x : α), r ≤ CoveringDesigns.indexedDegree B x) →
          (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
            (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
              (↑r : ℝ) ^ 2 ≤ (↑(Fintype.card ι) : ℝ) * (↑lam : ℝ) →
                CoveringDesigns.BoundaryIncidence.lowerCount (Fintype.card α) (Fintype.card ι) k r lam
                    (CoveringDesigns.BoundaryIncidence.eta B r)
                    (Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank) ≤
                  (↑(CoveringDesigns.BoundaryIncidence.regularPoints B r lam).card : ℝ))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.lowerCount_le
#print axioms CoveringDesigns.BoundaryIncidence.lowerCount_le

#check (@CoveringDesigns.BoundaryIncidence.row_membership_eq : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [Fintype ι]
  [inst : DecidableEq α] (B : ι → Finset α) {x y : α},
  CoveringDesigns.AffineCapacity.row B x = CoveringDesigns.AffineCapacity.row B y → ∀ (i : ι), x ∈ B i ↔ y ∈ B i)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.row_membership_eq
#print axioms CoveringDesigns.BoundaryIncidence.row_membership_eq

#check (@CoveringDesigns.BoundaryIncidence.supports_le : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  0 < Fintype.card ι →
    lam < r →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
            (↑r : ℝ) ^ 2 ≤ (↑(Fintype.card ι) : ℝ) * (↑lam : ℝ) →
              (Finset.image (CoveringDesigns.AffineCapacity.row B)
                    (CoveringDesigns.BoundaryIncidence.regularPoints B r lam)).card ≤
                2 ^ (Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank - 1))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.supports_le
#print axioms CoveringDesigns.BoundaryIncidence.supports_le

#check (@CoveringDesigns.BoundaryIncidence.dimension_le : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  0 < Fintype.card ι →
    lam < r →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
            (↑r : ℝ) ^ 2 ≤ (↑(Fintype.card ι) : ℝ) * (↑lam : ℝ) →
              CoveringDesigns.AffineCapacity.dimension
                  (CoveringDesigns.AffineCapacity.row B ''
                    (↑(CoveringDesigns.BoundaryIncidence.regularPoints B r lam) : Set α)) ≤
                Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank - 1)
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.dimension_le
#print axioms CoveringDesigns.BoundaryIncidence.dimension_le

#check (@CoveringDesigns.BoundaryIncidence.clone_bound : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  0 < Fintype.card ι →
    lam < r →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
            (↑r : ℝ) ^ 2 ≤ (↑(Fintype.card ι) : ℝ) * (↑lam : ℝ) →
              0 ≤ ((↑r : ℝ) + 1) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ) →
                ((↑r : ℝ) + 1 - (↑lam : ℝ)) * (↑(CoveringDesigns.BoundaryIncidence.regularPoints B r lam).card : ℝ) ≤
                  2 ^ (Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank - 1) *
                    (((↑r : ℝ) + 1) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ)))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.clone_bound
#print axioms CoveringDesigns.BoundaryIncidence.clone_bound

#check (@CoveringDesigns.BoundaryIncidence.clone_obstruction : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam : ℕ},
  0 < Fintype.card ι →
    lam < r →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x : α), r ≤ CoveringDesigns.indexedDegree B x) →
          (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
            (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
              (↑r : ℝ) ^ 2 ≤ (↑(Fintype.card ι) : ℝ) * (↑lam : ℝ) →
                0 <
                    CoveringDesigns.BoundaryIncidence.lowerCount (Fintype.card α) (Fintype.card ι) k r lam
                      (CoveringDesigns.BoundaryIncidence.eta B r)
                      (Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank) →
                  (↑r : ℝ) + 1 - (↑lam : ℝ) ≤ ((↑r : ℝ) + 1) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ) ∧
                    ((↑r : ℝ) + 1 - (↑lam : ℝ)) *
                        CoveringDesigns.BoundaryIncidence.lowerCount (Fintype.card α) (Fintype.card ι) k r lam
                          (CoveringDesigns.BoundaryIncidence.eta B r)
                          (Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank) ≤
                      2 ^ (Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank - 1) *
                        (((↑r : ℝ) + 1) * (↑k : ℝ) - (↑lam : ℝ) * (↑(Fintype.card α) : ℝ)))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.clone_obstruction
#print axioms CoveringDesigns.BoundaryIncidence.clone_obstruction

#check (@CoveringDesigns.BoundaryIncidence.covering_obstruction : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) {k r lam t : ℕ},
  0 < Fintype.card ι →
    lam < r →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x : α), r ≤ CoveringDesigns.indexedDegree B x) →
          (∀ (x y : α), x ≠ y → lam ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
            (↑r : ℝ) * ((↑k : ℝ) - 1) - (↑lam : ℝ) * ((↑(Fintype.card α) : ℝ) - 1) = (↑r : ℝ) - (↑lam : ℝ) →
              (↑r : ℝ) ^ 2 ≤ (↑(Fintype.card ι) : ℝ) * (↑lam : ℝ) →
                1 ≤ t →
                  t ≤ Fintype.card α →
                    (∀ (U : Finset α), U.card = t → ∃ i, U ⊆ B i) →
                      Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank ≤ t →
                        CoveringDesigns.BoundaryIncidence.lowerCount (Fintype.card α) (Fintype.card ι) k r lam
                            (CoveringDesigns.BoundaryIncidence.eta B r)
                            (Fintype.card ι - (CoveringDesigns.BoundaryIncidence.incidence B r).rank) ≤
                          (↑k : ℝ))
#guard_standard_axioms CoveringDesigns.BoundaryIncidence.covering_obstruction
#print axioms CoveringDesigns.BoundaryIncidence.covering_obstruction

#check (@CoveringDesigns.TwoKMinusTwoCapacity.indexed_degree_ge_six : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] {k : ℕ} (B : ι → Finset α),
  Fintype.card α = 2 * k - 2 →
    5 ≤ k →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          ∀ (x : α), 6 ≤ CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoCapacity.indexed_degree_ge_six
#print axioms CoveringDesigns.TwoKMinusTwoCapacity.indexed_degree_ge_six

#check (@CoveringDesigns.TwoKMinusTwoCapacity.thirteen_budget : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] {k : ℕ} (B : ι → Finset α),
  Fintype.card α = 2 * k - 2 →
    33 ≤ k →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
          Fintype.card ι = 13 →
            (CoveringDesigns.BoundaryIncidence.lowPoints B 6).card =
                k - 14 + CoveringDesigns.BoundaryIncidence.eta B 6 ∧
              CoveringDesigns.BoundaryIncidence.positiveCount B 6 3 +
                        2 * (13 - (CoveringDesigns.BoundaryIncidence.incidence B 6).rank) +
                      CoveringDesigns.BoundaryIncidence.eta B 6 +
                    k ≤
                  40 ∧
                1 ≤ 13 - (CoveringDesigns.BoundaryIncidence.incidence B 6).rank ∧
                  4 * k + 6 * (13 - (CoveringDesigns.BoundaryIncidence.incidence B 6).rank) +
                      CoveringDesigns.BoundaryIncidence.eta B 6 ≤
                    (CoveringDesigns.BoundaryIncidence.regularPoints B 6 3).card + 108)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoCapacity.thirteen_budget
#print axioms CoveringDesigns.TwoKMinusTwoCapacity.thirteen_budget

#check (@CoveringDesigns.TwoKMinusTwoCapacity.no_thirteen : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] {k : ℕ} (B : ι → Finset α),
  Fintype.card α = 2 * k - 2 →
    33 ≤ k →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) → Fintype.card ι = 13 → False)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoCapacity.no_thirteen
#print axioms CoveringDesigns.TwoKMinusTwoCapacity.no_thirteen

#check (@CoveringDesigns.TwoKMinusTwoCapacity.indexed_fourteen_le_card : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] {k : ℕ} (B : ι → Finset α),
  Fintype.card α = 2 * k - 2 →
    33 ≤ k →
      (∀ (i : ι), (B i).card = k) →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) → 14 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoCapacity.indexed_fourteen_le_card
#print axioms CoveringDesigns.TwoKMinusTwoCapacity.indexed_fourteen_le_card

#check (@CoveringDesigns.TwoKMinusTwoCapacity.fourteen_le_card : ∀ {α : Type u_1} [inst : Fintype α] {k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 2 → 33 ≤ k → CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoCapacity.fourteen_le_card
#print axioms CoveringDesigns.TwoKMinusTwoCapacity.fourteen_le_card

#check (@CoveringDesigns.TwoKMinusTwoCapacity.attaining : ∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  Fintype.card α = 2 * k - 2 → 33 ≤ k → ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoCapacity.attaining
#print axioms CoveringDesigns.TwoKMinusTwoCapacity.attaining

#check (@CoveringDesigns.TwoKMinusTwoCapacity.exactness : ∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  Fintype.card α = 2 * k - 2 →
    33 ≤ k →
      (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
        ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoCapacity.exactness
#print axioms CoveringDesigns.TwoKMinusTwoCapacity.exactness

#check (@CoveringDesigns.TwoKMinusTwoCapacity.covering_number : ∀ {k : ℕ},
  33 ≤ k →
    (∃ C : CoveringDesigns.Family (Fin (2*k-2)), CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family (Fin (2 * k - 2))), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoCapacity.covering_number
#print axioms CoveringDesigns.TwoKMinusTwoCapacity.covering_number

#check (@CoveringDesigns.C64_33_3.exactness_on : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 64 →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 33 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 33 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C64_33_3.exactness_on
#print axioms CoveringDesigns.C64_33_3.exactness_on

#check (@CoveringDesigns.covering_number_64_33_3 : (∃ C : CoveringDesigns.Family (Fin 64), CoveringDesigns.IsCover C 33 3 ∧ Finset.card C = 14) ∧
  ∀ (C : CoveringDesigns.Family (Fin 64)), CoveringDesigns.IsCover C 33 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.covering_number_64_33_3
#print axioms CoveringDesigns.covering_number_64_33_3

#check (@CoveringDesigns.C66_34_3.exactness_on : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 66 →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 34 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 34 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C66_34_3.exactness_on
#print axioms CoveringDesigns.C66_34_3.exactness_on

#check (@CoveringDesigns.covering_number_66_34_3 : (∃ C : CoveringDesigns.Family (Fin 66), CoveringDesigns.IsCover C 34 3 ∧ Finset.card C = 14) ∧
  ∀ (C : CoveringDesigns.Family (Fin 66)), CoveringDesigns.IsCover C 34 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.covering_number_66_34_3
#print axioms CoveringDesigns.covering_number_66_34_3

end CapacityContracts

namespace CoveringDesigns.AuditRankSlackCapacity
attribute [local instance] Classical.propDecidable

/-- Occurrence multiplicity expanded; no triple, injectivity, degree or budget premise. -/
theorem indexed_explicit {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]
    (B : ι → Finset α) {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k)
    (hsize : ∀ i, (B i).card = k)
    (hp : ∀ x y, x ≠ y →
      3 ≤ (Finset.univ.filter fun i => x ∈ B i ∧ y ∈ B i).card) :
    14 ≤ Fintype.card ι := by
  apply TwoKMinusTwoCapacity.indexed_fourteen_le_card B hv hk hsize
  intro x y hxy
  simpa only [indexedSubsetDegree, Finset.insert_subset_iff,
    Finset.singleton_subset_iff] using hp x y hxy

/-- Ordinary exactness expanded into finite sets of distinct finite blocks. -/
theorem exactness_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k) :
    (∃ C : Finset (Finset α),
      (∀ B ∈ C, B.card = k) ∧
      (∀ U : Finset α, U.card = 3 → ∃ B ∈ C, U ⊆ B) ∧ C.card = 14) ∧
    (∀ C : Finset (Finset α),
      (∀ B ∈ C, B.card = k) →
      (∀ U : Finset α, U.card = 3 → ∃ B ∈ C, U ⊆ B) → 14 ≤ C.card) := by
  obtain ⟨⟨C, hC, hc⟩, hl⟩ := TwoKMinusTwoCapacity.exactness hv hk
  exact ⟨⟨C, hC.1, hC.2, hc⟩, fun D hs ht => hl D ⟨hs, ht⟩⟩

#guard_standard_axioms indexed_explicit exactness_explicit
#print axioms indexed_explicit
#print axioms exactness_explicit
end CoveringDesigns.AuditRankSlackCapacity
