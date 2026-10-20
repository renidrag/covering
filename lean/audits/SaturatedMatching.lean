import CoveringDesigns.SaturatedMatching

/-! Full public contract snapshots, definition inspection and transitive
foundational axiom checks. Formalisation: Rob Gardiner with AI assistance. -/
section MatchingContracts
attribute [local instance] Classical.propDecidable
open Finset Matrix
open scoped BigOperators
set_option linter.unusedVariables false
universe u_1 u_2 u_3 u_4

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.indexedDegree
#print CoveringDesigns.indexedSubsetDegree
#print CoveringDesigns.AffineCapacity.dimension
#print CoveringDesigns.AffineCapacity.row
#print CoveringDesigns.SaturatedMatching.Split
#print CoveringDesigns.SaturatedMatching.Split.X
#print CoveringDesigns.SaturatedMatching.Split.Y
#print CoveringDesigns.SaturatedMatching.Split.P
#print CoveringDesigns.SaturatedMatching.Split.Q
#print CoveringDesigns.SaturatedMatching.Split.N
#print CoveringDesigns.SaturatedMatching.Split.cap
#print CoveringDesigns.SaturatedMatching.Split.weight
#print CoveringDesigns.SaturatedMatching.Split.loss
#print CoveringDesigns.SaturatedMatching.Split.excess
#print CoveringDesigns.SaturatedMatching.Split.crosses
#print CoveringDesigns.SaturatedMatching.Pattern
#print CoveringDesigns.SaturatedMatching.Pattern.named
#print CoveringDesigns.SaturatedMatching.Pattern.free
#print CoveringDesigns.SaturatedMatching.Remaining
#print CoveringDesigns.SaturatedMatching.Remaining.signature
#print CoveringDesigns.SaturatedMatching.FourCompatibility
#print CoveringDesigns.SaturatedMatching.Pattern.labels
#print CoveringDesigns.SaturatedMatching.Pattern.relabel
#print CoveringDesigns.SaturatedMatching.Remaining.relabel
#print CoveringDesigns.SaturatedMatching.FourCompatibility.relabel
#print CoveringDesigns.SaturatedMatching.normalizedSigns
#print CoveringDesigns.SaturatedMatching.CoverMatching
#print CoveringDesigns.SaturatedMatching.CoverMatching.block
#print CoveringDesigns.SaturatedMatching.CoverMatching.pattern
#print CoveringDesigns.SaturatedMatching.Split.matchingPoint
#print CoveringDesigns.SaturatedMatching.Split.matching

#check (@CoveringDesigns.AffineCapacity.affine_coefficients : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι] [inst : Fintype κ]
  (p : κ → ι → ℝ) {z : ι → ℝ}, z ∈ affineSpan ℝ (Set.range p) → ∃ (w : κ → ℝ), ∑ j : κ, w j = 1 ∧ z = ∑ j : κ, w j • p j)
#guard_standard_axioms CoveringDesigns.AffineCapacity.affine_coefficients
#print axioms CoveringDesigns.AffineCapacity.affine_coefficients

#check (@CoveringDesigns.AffineCapacity.omitted_coordinate : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι] [inst : Fintype κ]
  [inst_1 : DecidableEq κ] (p : κ → ι → ℝ) (a : κ → ι) (w : κ → ℝ),
  (∀ (i j : κ), p j (a i) = if i = j then 0 else 1) → ∑ j : κ, w j = 1 → ∀ (i : κ), (∑ j : κ, w j • p j) (a i) = 1 - w i)
#guard_standard_axioms CoveringDesigns.AffineCapacity.omitted_coordinate
#print axioms CoveringDesigns.AffineCapacity.omitted_coordinate

#check (@CoveringDesigns.AffineCapacity.omitted_coordinates_rigidity : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
  [inst : DecidableEq κ] (p : κ → ι → ℝ) (a : κ → ι),
  (∀ (i j : κ), p j (a i) = if i = j then 0 else 1) →
    ∀ {z : ι → ℝ}, z ∈ affineSpan ℝ (Set.range p) → (∀ (i : ι), z i = 0 ∨ z i = 1) → ∃ (j : κ), z = p j)
#guard_standard_axioms CoveringDesigns.AffineCapacity.omitted_coordinates_rigidity
#print axioms CoveringDesigns.AffineCapacity.omitted_coordinates_rigidity

#check (@CoveringDesigns.AffineCapacity.omitted_coordinates_independent : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι]
  [Fintype κ] [inst : DecidableEq κ] (p : κ → ι → ℝ) (a : κ → ι),
  (∀ (i j : κ), p j (a i) = if i = j then 0 else 1) → AffineIndependent ℝ p)
#guard_standard_axioms CoveringDesigns.AffineCapacity.omitted_coordinates_independent
#print axioms CoveringDesigns.AffineCapacity.omitted_coordinates_independent

#check (@CoveringDesigns.AffineCapacity.boundary_dichotomy : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype ι]
  [inst_1 : Fintype α] [inst_2 : DecidableEq α] (B : ι → Finset α) (F : Finset α) {t : ℕ},
  F.Nonempty →
    1 ≤ t →
      t ≤ Fintype.card α →
        (∀ (U : Finset α), U.card = t → ∃ (i : ι), U ⊆ B i) →
          CoveringDesigns.AffineCapacity.dimension (CoveringDesigns.AffineCapacity.row B '' (↑F : Set α)) ≤ t →
            (∃ (i : ι), F ⊆ B i) ∨
              (¬∃ (i : ι), F ⊆ B i) ∧
                CoveringDesigns.AffineCapacity.dimension (CoveringDesigns.AffineCapacity.row B '' (↑F : Set α)) = t ∧
                  ∃ S ⊆ F,
                    S.card = t + 1 ∧
                      (AffineIndependent ℝ fun (x : ↥S) => CoveringDesigns.AffineCapacity.row B (↑x : α)) ∧
                        CoveringDesigns.AffineCapacity.row B '' (↑F : Set α) =
                            CoveringDesigns.AffineCapacity.row B '' (↑S : Set α) ∧
                          ∀ x ∈ S,
                            ∃ (i : ι),
                              B i ∩ F =
                                {y ∈ F |
                                  CoveringDesigns.AffineCapacity.row B y ≠ CoveringDesigns.AffineCapacity.row B x})
#guard_standard_axioms CoveringDesigns.AffineCapacity.boundary_dichotomy
#print axioms CoveringDesigns.AffineCapacity.boundary_dichotomy

#check (@CoveringDesigns.AffineCapacity.boundary_supports : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype ι]
  [inst_1 : Fintype α] [inst_2 : DecidableEq α] (B : ι → Finset α) (F : Finset α) {t : ℕ},
  F.Nonempty →
    1 ≤ t →
      t ≤ Fintype.card α →
        (∀ (U : Finset α), U.card = t → ∃ (i : ι), U ⊆ B i) →
          CoveringDesigns.AffineCapacity.dimension (CoveringDesigns.AffineCapacity.row B '' (↑F : Set α)) ≤ t →
            (¬∃ (i : ι), F ⊆ B i) →
              (Finset.image (CoveringDesigns.AffineCapacity.row B) F).card = t + 1 ∧
                ∀ r ∈ Finset.image (CoveringDesigns.AffineCapacity.row B) F,
                  {x ∈ F | CoveringDesigns.AffineCapacity.row B x = r}.Nonempty ∧
                    ∃ (i : ι), B i ∩ F = {x ∈ F | CoveringDesigns.AffineCapacity.row B x ≠ r})
#guard_standard_axioms CoveringDesigns.AffineCapacity.boundary_supports
#print axioms CoveringDesigns.AffineCapacity.boundary_supports

#check (@CoveringDesigns.AffineCapacity.card_mul_le_of_dimension_le : ∀ {α : Type u_1} {ι : Type u_2} [Fintype ι]
  [inst : Fintype α] [inst_1 : DecidableEq α] (B : ι → Finset α) (F : Finset α) {t k : ℕ},
  1 ≤ t →
    t ≤ Fintype.card α →
      (∀ (U : Finset α), U.card = t → ∃ (i : ι), U ⊆ B i) →
        (∀ (i : ι), (B i).card ≤ k) →
          CoveringDesigns.AffineCapacity.dimension (CoveringDesigns.AffineCapacity.row B '' (↑F : Set α)) ≤ t →
            t * F.card ≤ (t + 1) * k)
#guard_standard_axioms CoveringDesigns.AffineCapacity.card_mul_le_of_dimension_le
#print axioms CoveringDesigns.AffineCapacity.card_mul_le_of_dimension_le

#check (@CoveringDesigns.AffineCapacity.card_le_max_of_fibres : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype ι]
  [inst_1 : Fintype α] [inst_2 : DecidableEq α] (B : ι → Finset α) (F : Finset α) {t k M : ℕ},
  1 ≤ t →
    t ≤ Fintype.card α →
      (∀ (U : Finset α), U.card = t → ∃ (i : ι), U ⊆ B i) →
        (∀ (i : ι), (B i).card ≤ k) →
          CoveringDesigns.AffineCapacity.dimension (CoveringDesigns.AffineCapacity.row B '' (↑F : Set α)) ≤ t →
            (∀ r ∈ Finset.image (CoveringDesigns.AffineCapacity.row B) F,
                {x ∈ F | CoveringDesigns.AffineCapacity.row B x = r}.card ≤ M) →
              F.card ≤ max k ((t + 1) * M))
#guard_standard_axioms CoveringDesigns.AffineCapacity.card_le_max_of_fibres
#print axioms CoveringDesigns.AffineCapacity.card_le_max_of_fibres

#check (@CoveringDesigns.SaturatedMatching.boundary_six : ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α] {k : ℕ},
  Fintype.card α = 2 * k - 2 → 3 ≤ k → 6 * ((↑k : ℝ) - 1) - 3 * ((↑(Fintype.card α) : ℝ) - 1) = 6 - 3)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.boundary_six
#print axioms CoveringDesigns.SaturatedMatching.boundary_six

#check (@CoveringDesigns.SaturatedMatching.thirteen_budget : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] {k : ℕ} (B : ι → Finset α),
  Fintype.card α = 2 * k - 2 →
    14 ≤ k →
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
#guard_standard_axioms CoveringDesigns.SaturatedMatching.thirteen_budget
#print axioms CoveringDesigns.SaturatedMatching.thirteen_budget

#check (@CoveringDesigns.SaturatedMatching.regular_fibre_le_nine : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] {k : ℕ} (B : ι → Finset α),
  Fintype.card α = 2 * k - 2 →
    31 ≤ k →
      k ≤ 32 →
        (∀ (i : ι), (B i).card = k) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
            ∀
              r ∈
                Finset.image (CoveringDesigns.AffineCapacity.row B)
                  (CoveringDesigns.BoundaryIncidence.regularPoints B 6 3),
              {x ∈ CoveringDesigns.BoundaryIncidence.regularPoints B 6 3 |
                    CoveringDesigns.AffineCapacity.row B x = r}.card ≤
                9)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.regular_fibre_le_nine
#print axioms CoveringDesigns.SaturatedMatching.regular_fibre_le_nine

#check (@CoveringDesigns.SaturatedMatching.no_thirteen_of_pair_floor : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] {k : ℕ} (B : ι → Finset α),
  Fintype.card α = 2 * k - 2 →
    31 ≤ k →
      k ≤ 32 →
        (∀ (i : ι), (B i).card = k) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, y}) →
            (∀ (U : Finset α), U.card = 3 → ∃ (i : ι), U ⊆ B i) → Fintype.card ι = 13 → False)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.no_thirteen_of_pair_floor
#print axioms CoveringDesigns.SaturatedMatching.no_thirteen_of_pair_floor

#check (@CoveringDesigns.SaturatedMatching.Split.cross_endpoints : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} (s : CoveringDesigns.SaturatedMatching.Split C p q 31) (z : ↥s.crosses),
  (↑z : α × α).1 ≠ p ∧ (↑z : α × α).1 ≠ q ∧ (↑z : α × α).2 ≠ p ∧ (↑z : α × α).2 ≠ q ∧ (↑z : α × α).1 ≠ (↑z : α × α).2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.cross_endpoints
#print axioms CoveringDesigns.SaturatedMatching.Split.cross_endpoints

#check (@CoveringDesigns.SaturatedMatching.Split.matching_endpoints : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α}
  (s : CoveringDesigns.SaturatedMatching.Split C p q 31) (e : Option ↥s.crosses),
  s.matchingPoint (e, true) ≠ s.matchingPoint (e, false))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.matching_endpoints
#print axioms CoveringDesigns.SaturatedMatching.Split.matching_endpoints

#check (@CoveringDesigns.SaturatedMatching.Split.matching_separate : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α}
  (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        ∀ (e f : Option ↥s.crosses), e ≠ f → ∀ (b c : Bool), s.matchingPoint (e, b) ≠ s.matchingPoint (f, c))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.matching_separate
#print axioms CoveringDesigns.SaturatedMatching.Split.matching_separate

#check (@CoveringDesigns.SaturatedMatching.Split.matching_injective : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α}
  (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 → CoveringDesigns.IsCover C 31 3 → Finset.card C = 13 → Function.Injective s.matchingPoint)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.matching_injective
#print axioms CoveringDesigns.SaturatedMatching.Split.matching_injective

#check (@CoveringDesigns.SaturatedMatching.Split.matching_complete : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α}
  (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        ∀ (x y : α),
          x ≠ y →
            CoveringDesigns.degree (CoveringDesigns.star C x) y = 2 →
              ∃ (e : Option ↥s.crosses), ({x, y} : Finset α) = {s.matchingPoint (e, true), s.matchingPoint (e, false)})
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.matching_complete
#print axioms CoveringDesigns.SaturatedMatching.Split.matching_complete

#check (@CoveringDesigns.SaturatedMatching.Split.matching_card : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 → Fintype.card (Option ↥s.crosses) = 4 ∨ Fintype.card (Option ↥s.crosses) = 5)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.matching_card
#print axioms CoveringDesigns.SaturatedMatching.Split.matching_card

#check (@CoveringDesigns.SaturatedMatching.cross_excess_identity : ∀ {γ : Type u_1} (T : Finset γ) (μ : γ → ℕ),
  (∀ z ∈ T, 2 ≤ μ z) → ∑ z ∈ T, μ z + {z ∈ T | μ z = 2}.card = 3 * T.card + ∑ z ∈ T, (μ z - 3))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.cross_excess_identity
#print axioms CoveringDesigns.SaturatedMatching.cross_excess_identity

#check (@CoveringDesigns.SaturatedMatching.loss_identity : ∀ {β : Type u_1} [DecidableEq β] (A : Finset β) (w cap : β → ℕ),
  (∀ i ∈ A, w i ≤ cap i) → ∑ i ∈ A, (cap i - w i) + ∑ i ∈ A, w i = ∑ i ∈ A, cap i)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.loss_identity
#print axioms CoveringDesigns.SaturatedMatching.loss_identity

#check (@CoveringDesigns.SaturatedMatching.cross_loss_identity : ∀ {β : Type u_1} {γ : Type u_2} [DecidableEq β] (T : Finset γ)
  (A : Finset β) (μ : γ → ℕ) (w cap : β → ℕ),
  (∀ z ∈ T, 2 ≤ μ z) →
    (∀ i ∈ A, w i ≤ cap i) →
      ∑ z ∈ T, μ z = ∑ i ∈ A, w i →
        ∑ i ∈ A, (cap i - w i) + ∑ z ∈ T, (μ z - 3) + 3 * T.card = ∑ i ∈ A, cap i + {z ∈ T | μ z = 2}.card)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.cross_loss_identity
#print axioms CoveringDesigns.SaturatedMatching.cross_loss_identity

#check (@CoveringDesigns.SaturatedMatching.balanced_of_loss_zero : ∀ {β : Type u_1} [DecidableEq β] (A : Finset β)
  (w cap : β → ℕ), (∀ i ∈ A, w i ≤ cap i) → ∑ i ∈ A, (cap i - w i) = 0 → ∀ i ∈ A, w i = cap i)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.balanced_of_loss_zero
#print axioms CoveringDesigns.SaturatedMatching.balanced_of_loss_zero

#check (@CoveringDesigns.SaturatedMatching.capacity_loss_at : ∀ {β : Type u_1} [DecidableEq β] (A : Finset β) (w cap : β → ℕ),
  (∀ i ∈ A, w i ≤ cap i) → ∀ {i : β}, i ∈ A → ∑ j ∈ A, w j + (cap i - w i) ≤ ∑ j ∈ A, cap j)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.capacity_loss_at
#print axioms CoveringDesigns.SaturatedMatching.capacity_loss_at

#check (@CoveringDesigns.SaturatedMatching.shared_block_bound : ∀ {β : Type u_1} [DecidableEq β] {Q R : Finset β} (I : β → ℕ)
  {k : ℕ},
  3 ≤ k →
    2 ≤ Q.card →
      R ⊆ Q →
        2 * (k - 1) ≤ ∑ D ∈ Q, I D →
          (∀ D ∈ R, I D = 2) → (∀ D ∈ Q, I D ≤ k - 1) → (k - 3) * R.card ≤ (Q.card - 2) * (k - 1))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.shared_block_bound
#print axioms CoveringDesigns.SaturatedMatching.shared_block_bound

#check (@CoveringDesigns.SaturatedMatching.assignment_fibre_bound : ∀ {β : Type u_1} {γ : Type u_2} [inst : DecidableEq β]
  {P Q : Finset β} {T : Finset γ} (f : γ → β × β) (I : β → β → ℕ) {k : ℕ},
  3 ≤ k →
    2 ≤ Q.card →
      (∀ z ∈ T, (f z).1 ∈ P ∧ (f z).2 ∈ Q) →
        Set.InjOn f (↑T : Set γ) →
          (∀ A ∈ P, 2 * (k - 1) ≤ ∑ E ∈ Q, I A E) →
            (∀ z ∈ T, I (f z).1 (f z).2 = 2) →
              (∀ A ∈ P, ∀ E ∈ Q, I A E ≤ k - 1) → ∀ A ∈ P, (k - 3) * {z ∈ T | (f z).1 = A}.card ≤ (Q.card - 2) * (k - 1))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.assignment_fibre_bound
#print axioms CoveringDesigns.SaturatedMatching.assignment_fibre_bound

#check (@CoveringDesigns.SaturatedMatching.assignment_total_bound : ∀ {β : Type u_1} {γ : Type u_2} [DecidableEq β]
  {P Q : Finset β} {T : Finset γ} (f : γ → β × β) (I : β → β → ℕ) {k : ℕ},
  3 ≤ k →
    2 ≤ Q.card →
      (∀ z ∈ T, (f z).1 ∈ P ∧ (f z).2 ∈ Q) →
        Set.InjOn f (↑T : Set γ) →
          (∀ A ∈ P, 2 * (k - 1) ≤ ∑ E ∈ Q, I A E) →
            (∀ z ∈ T, I (f z).1 (f z).2 = 2) →
              (∀ A ∈ P, ∀ E ∈ Q, I A E ≤ k - 1) → (k - 3) * T.card ≤ P.card * ((Q.card - 2) * (k - 1)))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.assignment_total_bound
#print axioms CoveringDesigns.SaturatedMatching.assignment_total_bound

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.cross_card_bound : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C) (e : M), (T.split e).crosses.card ≤ Fintype.card M - 1)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.cross_card_bound
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.cross_card_bound

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.four_zero : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 → Fintype.card M = 4 → ∀ (e : M), (T.split e).loss = 0 ∧ (T.split e).excess = 0)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.four_zero
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.four_zero

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.cross_exact : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        Fintype.card M = 4 →
          ∀ (e : M) {x y : α},
            x ∈ (T.split e).X →
              y ∈ (T.split e).Y →
                3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y →
                  CoveringDesigns.degree (CoveringDesigns.star C x) y = 3)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.cross_exact
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.cross_exact

#check (@CoveringDesigns.SaturatedMatching.Split.balanced_intersections : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α}
  (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  CoveringDesigns.IsCover C 31 3 →
    s.loss = 0 → ∀ {A : Finset α}, A ∈ C → (p ∈ A ↔ q ∉ A) → (s.left ∩ A).card = 16 ∧ (s.right ∩ A).card = 16)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.balanced_intersections
#print axioms CoveringDesigns.SaturatedMatching.Split.balanced_intersections

#check (@CoveringDesigns.SaturatedMatching.Split.orient_cross : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} (s : CoveringDesigns.SaturatedMatching.Split C p q 31) {x y : α},
  x ≠ p ∧ x ≠ q → y ≠ p ∧ y ≠ q → (x ∈ s.left ↔ y ∉ s.left) → ∃ z ∈ s.X ×ˢ s.Y, ({z.1, z.2} : Finset α) = {x, y})
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.orient_cross
#print axioms CoveringDesigns.SaturatedMatching.Split.orient_cross

#check (@CoveringDesigns.SaturatedMatching.Split.excess_two : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} (s : CoveringDesigns.SaturatedMatching.Split C p q 31) {z w : α × α},
  z ∈ s.X ×ˢ s.Y →
    w ∈ s.X ×ˢ s.Y →
      z ≠ w →
        CoveringDesigns.degree (CoveringDesigns.star C z.1) z.2 = 4 →
          CoveringDesigns.degree (CoveringDesigns.star C w.1) w.2 = 4 → 2 ≤ s.excess)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.excess_two
#print axioms CoveringDesigns.SaturatedMatching.Split.excess_two

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.not_five : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C),
  Fintype.card α = 60 → CoveringDesigns.IsCover C 31 3 → Finset.card C = 13 → Fintype.card M = 5 → False)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.not_five
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.not_five

#check (@CoveringDesigns.SaturatedMatching.Split.residual_of_separated : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α}
  (s : CoveringDesigns.SaturatedMatching.Split C p q 31) {x y : α},
  x ≠ p ∧ x ≠ q → y ≠ p ∧ y ≠ q → (x ∈ s.left ↔ y ∉ s.left) → x ∈ s.X ∧ y ∈ s.Y ∨ x ∈ s.Y ∧ y ∈ s.X)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.residual_of_separated
#print axioms CoveringDesigns.SaturatedMatching.Split.residual_of_separated

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.four_compatibility : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype M] [inst_3 : DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C) (hv : Fintype.card α = 60)
  (hC : CoveringDesigns.IsCover C 31 3) (hb : Finset.card C = 13),
  Fintype.card M = 4 → CoveringDesigns.SaturatedMatching.FourCompatibility (T.pattern hv hC hb))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.four_compatibility
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.four_compatibility

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.supporting_intersection_sixteen : ∀ {α : Type u_1} {M : Type u_2}
  [inst : Fintype α] [inst_1 : DecidableEq α] [inst_2 : Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        Fintype.card M = 4 →
          ∀ (e f : M),
            e ≠ f → ∀ (a b : Bool), ((↑(T.block (e, a)) : Finset α) ∩ (↑(T.block (f, b)) : Finset α)).card = 16)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.supporting_intersection_sixteen
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.supporting_intersection_sixteen

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.not_four : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C),
  Fintype.card α = 60 → CoveringDesigns.IsCover C 31 3 → Finset.card C = 13 → Fintype.card M = 4 → False)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.not_four
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.not_four

#check (@CoveringDesigns.SaturatedMatching.family_degree : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (x : α),
  CoveringDesigns.indexedDegree (fun (A : ↥C) => (↑A : Finset α)) x = CoveringDesigns.degree C x)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.family_degree
#print axioms CoveringDesigns.SaturatedMatching.family_degree

#check (@CoveringDesigns.SaturatedMatching.Split.endpoints_left : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  p ∈ s.left ∧ q ∈ s.left)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.endpoints_left
#print axioms CoveringDesigns.SaturatedMatching.Split.endpoints_left

#check (@CoveringDesigns.SaturatedMatching.Split.endpoints_right : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  p ∈ s.right ∧ q ∈ s.right)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.endpoints_right
#print axioms CoveringDesigns.SaturatedMatching.Split.endpoints_right

#check (@CoveringDesigns.SaturatedMatching.Split.complementary : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k) (x : α),
  x ≠ p → x ≠ q → (x ∈ s.left ↔ x ∉ s.right))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.complementary
#print axioms CoveringDesigns.SaturatedMatching.Split.complementary

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.point_ne : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C) {e f : M},
  e ≠ f → ∀ (b c : Bool), T.point (e, b) ≠ T.point (f, c))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.point_ne
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.point_ne

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.own_mem : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C) (e : M) (a b : Bool),
  T.point (e, b) ∈ (↑(T.block (e, a)) : Finset α))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.own_mem
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.own_mem

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.block_injective : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C),
  Fintype.card α = 60 → CoveringDesigns.IsCover C 31 3 → Finset.card C = 13 → Function.Injective T.block)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.block_injective
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.block_injective

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.endpoint_degree : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        ∀ (f : M) (b : Bool), CoveringDesigns.indexedDegree (fun (A : ↥C) => (↑A : Finset α)) (T.point (f, b)) = 6)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.endpoint_degree
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.endpoint_degree

#check (@CoveringDesigns.SaturatedMatching.CoverMatching.pair_floor : ∀ {α : Type u_1} {M : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [Fintype M] [DecidableEq M] {C : CoveringDesigns.Family α}
  (T : CoveringDesigns.SaturatedMatching.CoverMatching C),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        ∀ (x : α) (f : M) (b : Bool),
          x ≠ T.point (f, b) →
            x ≠ T.point (f, !b) →
              3 ≤ CoveringDesigns.indexedSubsetDegree (fun (A : ↥C) => (↑A : Finset α)) {x, T.point (f, b)})
#guard_standard_axioms CoveringDesigns.SaturatedMatching.CoverMatching.pair_floor
#print axioms CoveringDesigns.SaturatedMatching.CoverMatching.pair_floor

#check (@CoveringDesigns.SaturatedMatching.Split.endpoint_floor : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Fintype.card α = 2 * k - 2 → 9 ≤ k → CoveringDesigns.IsCover C k 3 → 4 ≤ Finset.card s.P ∧ 4 ≤ Finset.card s.Q)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.endpoint_floor
#print axioms CoveringDesigns.SaturatedMatching.Split.endpoint_floor

#check (@CoveringDesigns.SaturatedMatching.Split.no_second_partner : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α} {k : ℕ}
  (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Fintype.card α = 2 * k - 2 →
    k = 31 ∨ k = 32 →
      CoveringDesigns.IsCover C k 3 →
        Finset.card C = 13 → ∀ (z : α), z ≠ p → z ≠ q → CoveringDesigns.degree (CoveringDesigns.star C q) z ≠ 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.no_second_partner
#print axioms CoveringDesigns.SaturatedMatching.Split.no_second_partner

#check (@CoveringDesigns.SaturatedMatching.Split.endpoint_counts : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Fintype.card α = 2 * k - 2 →
    k = 31 ∨ k = 32 →
      CoveringDesigns.IsCover C k 3 →
        Finset.card C = 13 →
          Finset.card s.P = 4 ∧ Finset.card s.Q = 4 ∨
            k = 31 ∧ Finset.card s.P = 4 ∧ Finset.card s.Q = 5 ∨ k = 31 ∧ Finset.card s.P = 5 ∧ Finset.card s.Q = 4)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.endpoint_counts
#print axioms CoveringDesigns.SaturatedMatching.Split.endpoint_counts

#check (@CoveringDesigns.SaturatedMatching.Split.surviving_counts : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Fintype.card α = 2 * k - 2 →
    k = 31 ∨ k = 32 →
      CoveringDesigns.IsCover C k 3 →
        Finset.card C = 13 →
          k = 31 ∧
            Finset.card s.P = 4 ∧
              Finset.card s.Q = 4 ∧ CoveringDesigns.degree C p = 6 ∧ CoveringDesigns.degree C q = 6 ∧ s.crosses.card ≤ 8)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.surviving_counts
#print axioms CoveringDesigns.SaturatedMatching.Split.surviving_counts

#check (@CoveringDesigns.SaturatedMatching.no_saturation_32 : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α},
  Fintype.card α = 62 →
    CoveringDesigns.IsCover C 32 3 →
      Finset.card C = 13 → p ≠ q → CoveringDesigns.degree (CoveringDesigns.star C p) q ≠ 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.no_saturation_32
#print axioms CoveringDesigns.SaturatedMatching.no_saturation_32

#check (@CoveringDesigns.TwoKMinusTwoMatching.fourteen_le_card : ∀ {α : Type u_1} [inst : Fintype α] {k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 2 → 31 ≤ k → CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoMatching.fourteen_le_card
#print axioms CoveringDesigns.TwoKMinusTwoMatching.fourteen_le_card

#check (@CoveringDesigns.TwoKMinusTwoMatching.attaining : ∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  Fintype.card α = 2 * k - 2 →
    31 ≤ k → ∃ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoMatching.attaining
#print axioms CoveringDesigns.TwoKMinusTwoMatching.attaining

#check (@CoveringDesigns.TwoKMinusTwoMatching.exactness_on : ∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  Fintype.card α = 2 * k - 2 →
    31 ≤ k →
      (∃ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
        ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoMatching.exactness_on
#print axioms CoveringDesigns.TwoKMinusTwoMatching.exactness_on

#check (@CoveringDesigns.TwoKMinusTwoMatching.covering_number : ∀ {k : ℕ},
  31 ≤ k →
    (∃ (C : CoveringDesigns.Family (Fin (2 * k - 2))), CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family (Fin (2 * k - 2))), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.TwoKMinusTwoMatching.covering_number
#print axioms CoveringDesigns.TwoKMinusTwoMatching.covering_number

#check (@CoveringDesigns.SaturatedMatching.five_pair_excess : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [DecidableEq ι] [DecidableEq M] {B : ι → Finset α}
  (P : CoveringDesigns.SaturatedMatching.Pattern B),
  Fintype.card M = 5 →
    (∀ (f : M) (b : Bool), CoveringDesigns.indexedDegree B (P.point (f, b)) = 6) →
      (∀ (f g : M),
          f ≠ g → ∀ (b c : Bool), 3 ≤ CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)}) →
        ∀ (f g : M),
          f ≠ g →
            ∃ (e : M),
              e ≠ f ∧
                e ≠ g ∧
                  ∃ (b : Bool) (c : Bool),
                    CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)} = 4 ∧
                      CoveringDesigns.indexedSubsetDegree B {P.point (f, !b), P.point (g, !c)} = 4 ∧
                        (∀ (a : Bool), P.point (f, b) ∈ B (P.block (e, a)) ↔ P.point (g, c) ∉ B (P.block (e, a))) ∧
                          ∀ (a : Bool), P.point (f, !b) ∈ B (P.block (e, a)) ↔ P.point (g, !c) ∉ B (P.block (e, a)))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.five_pair_excess
#print axioms CoveringDesigns.SaturatedMatching.five_pair_excess

#check (@CoveringDesigns.SaturatedMatching.four_pair_small_intersection : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B),
  CoveringDesigns.SaturatedMatching.FourCompatibility P →
    (∀ (x : α) (f : M) (b : Bool),
        x ≠ P.point (f, b) → x ≠ P.point (f, !b) → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, P.point (f, b)}) →
      ∃ (e : M) (f : M), e ≠ f ∧ ∃ (a : Bool) (b : Bool), (B (P.block (e, a)) ∩ B (P.block (f, b))).card = 4)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.four_pair_small_intersection
#print axioms CoveringDesigns.SaturatedMatching.four_pair_small_intersection

#check (@CoveringDesigns.SaturatedMatching.four_rest : ∀ {M : Type u_1} [inst : Fintype M] [inst_1 : DecidableEq M],
  Fintype.card M = 4 → ∀ {e h f g : M}, e ≠ h → e ≠ f → e ≠ g → h ≠ f → h ≠ g → f ≠ g → Finset.univ \ {f, g} = {e, h})
#guard_standard_axioms CoveringDesigns.SaturatedMatching.four_rest
#print axioms CoveringDesigns.SaturatedMatching.four_rest

#check (@CoveringDesigns.SaturatedMatching.Remaining.signatures_compatible : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P),
  CoveringDesigns.SaturatedMatching.FourCompatibility P →
    ∀ (f g : M), f ≠ g → R.signature f = R.signature g ∨ Disjoint (R.signature f) (R.signature g))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.signatures_compatible
#print axioms CoveringDesigns.SaturatedMatching.Remaining.signatures_compatible

#check (@CoveringDesigns.SaturatedMatching.Remaining.no_three_share : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P),
  CoveringDesigns.SaturatedMatching.FourCompatibility P →
    ∀ {f g h : M},
      f ≠ g →
        f ≠ h → g ≠ h → ∀ (b c d : Bool), R.index (f, b) = R.index (g, c) → R.index (f, b) = R.index (h, d) → False)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.no_three_share
#print axioms CoveringDesigns.SaturatedMatching.Remaining.no_three_share

#check (@CoveringDesigns.SaturatedMatching.Remaining.signature_fibre_le_two : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P),
  CoveringDesigns.SaturatedMatching.FourCompatibility P → ∀ (J : Finset ι), (Finset.univ.filter (fun f : M => R.signature f = J)).card ≤ 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.signature_fibre_le_two
#print axioms CoveringDesigns.SaturatedMatching.Remaining.signature_fibre_le_two

#check (@CoveringDesigns.SaturatedMatching.Remaining.two_groups : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P),
  CoveringDesigns.SaturatedMatching.FourCompatibility P →
    (Finset.image R.signature Finset.univ).card = 2 ∧
      ∀ J ∈ Finset.image R.signature Finset.univ, (Finset.univ.filter (fun f : M => R.signature f = J)).card = 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.two_groups
#print axioms CoveringDesigns.SaturatedMatching.Remaining.two_groups

#check (@CoveringDesigns.SaturatedMatching.Remaining.grouped_indices : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P),
  CoveringDesigns.SaturatedMatching.FourCompatibility P →
    ∃ (r : Fin 4 ≃ M),
      R.signature ((r : Fin 4 → M) 0) = R.signature ((r : Fin 4 → M) 1) ∧
        R.signature ((r : Fin 4 → M) 2) = R.signature ((r : Fin 4 → M) 3) ∧
          Disjoint (R.signature ((r : Fin 4 → M) 0)) (R.signature ((r : Fin 4 → M) 2)))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.grouped_indices
#print axioms CoveringDesigns.SaturatedMatching.Remaining.grouped_indices

#check (@CoveringDesigns.SaturatedMatching.Remaining.disjoint_correlations : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι]
  [inst_4 : DecidableEq M] {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P),
  CoveringDesigns.SaturatedMatching.FourCompatibility P →
    ∀ (e h f g : M),
      f ≠ g →
        e ≠ h →
          Finset.univ \ {f, g} = {e, h} →
            Disjoint (R.signature f) (R.signature g) → (P.sign e f == P.sign e g) ≠ (P.sign h f == P.sign h g))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.disjoint_correlations
#print axioms CoveringDesigns.SaturatedMatching.Remaining.disjoint_correlations

#check (@CoveringDesigns.SaturatedMatching.aligned_signs : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : Fintype ι]
  [inst_1 : DecidableEq α] [inst_2 : DecidableEq ι] {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern (M := Fin 4) B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P),
  CoveringDesigns.SaturatedMatching.FourCompatibility P →
    R.index (0, true) = R.index (1, true) →
      R.index (2, true) = R.index (3, true) →
        P.sign 2 0 ≠ P.sign 2 1 ∧ P.sign 3 0 ≠ P.sign 3 1 ∧ P.sign 0 2 ≠ P.sign 0 3 ∧ P.sign 1 2 ≠ P.sign 1 3)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.aligned_signs
#print axioms CoveringDesigns.SaturatedMatching.aligned_signs

#check (@CoveringDesigns.SaturatedMatching.normalized_from_aligned : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α]
  [inst : Fintype ι] [inst_1 : DecidableEq α] [inst_2 : DecidableEq ι] {B : ι → Finset α}
  {P : CoveringDesigns.SaturatedMatching.Pattern B} (R : CoveringDesigns.SaturatedMatching.Remaining P),
  CoveringDesigns.SaturatedMatching.FourCompatibility P →
    R.index (0, true) = R.index (1, true) →
      R.index (2, true) = R.index (3, true) →
        Disjoint (R.signature 0) (R.signature 2) →
          R.signature 1 = R.signature 0 →
            R.signature 3 = R.signature 2 →
              P.sign 0 2 = true ∧ P.sign 1 2 = true ∧ P.sign 2 0 = true ∧ P.sign 3 0 = true →
                have b := P.sign 1 0;
                ∀ (e f : Fin 4),
                  e ≠ f →
                    (P.relabel (Equiv.refl (Fin 4)) ![b, b, true, true] ![true, true, b, b]).sign e f =
                      CoveringDesigns.SaturatedMatching.normalizedSigns e f)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.normalized_from_aligned
#print axioms CoveringDesigns.SaturatedMatching.normalized_from_aligned

#check (@CoveringDesigns.SaturatedMatching.normalized_unmatched : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : Fintype ι]
  [inst_1 : DecidableEq α] [DecidableEq ι] {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B),
  (∀ (e f : Fin 4), e ≠ f → P.sign e f = CoveringDesigns.SaturatedMatching.normalizedSigns e f) →
    (∀ (f : Fin 4) (b : Bool), CoveringDesigns.indexedDegree B (P.point (f, b)) = 6) →
      (∀ (x : α) (f : Fin 4) (b : Bool),
          x ≠ P.point (f, b) → x ≠ P.point (f, !b) → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, P.point (f, b)}) →
        ∀ (x : α), (∀ (e : Fin 4) (b : Bool), x ≠ P.point (e, b)) → x ∉ B (P.block (0, true)) ∩ B (P.block (1, true)))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.normalized_unmatched
#print axioms CoveringDesigns.SaturatedMatching.normalized_unmatched

#check (@CoveringDesigns.SaturatedMatching.normalized_small_intersection : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α]
  [inst : Fintype ι] [inst_1 : DecidableEq α] [DecidableEq ι] {B : ι → Finset α}
  (P : CoveringDesigns.SaturatedMatching.Pattern B),
  (∀ (e f : Fin 4), e ≠ f → P.sign e f = CoveringDesigns.SaturatedMatching.normalizedSigns e f) →
    (∀ (f : Fin 4) (b : Bool), CoveringDesigns.indexedDegree B (P.point (f, b)) = 6) →
      (∀ (x : α) (f : Fin 4) (b : Bool),
          x ≠ P.point (f, b) → x ≠ P.point (f, !b) → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, P.point (f, b)}) →
        (B (P.block (0, true)) ∩ B (P.block (1, true))).card = 4)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.normalized_small_intersection
#print axioms CoveringDesigns.SaturatedMatching.normalized_small_intersection

#check (@CoveringDesigns.SaturatedMatching.Remaining.exists_of_four : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B),
  Fintype.card M = 4 →
    (∀ (f : M) (b : Bool), CoveringDesigns.indexedDegree B (P.point (f, b)) = 6) →
      Nonempty (CoveringDesigns.SaturatedMatching.Remaining P))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.exists_of_four
#print axioms CoveringDesigns.SaturatedMatching.Remaining.exists_of_four

#check (@CoveringDesigns.SaturatedMatching.Remaining.point_mem : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M] {B : ι → Finset α}
  {P : CoveringDesigns.SaturatedMatching.Pattern B} (R : CoveringDesigns.SaturatedMatching.Remaining P) (z : M × Bool),
  P.point z ∈ B (R.index z))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.point_mem
#print axioms CoveringDesigns.SaturatedMatching.Remaining.point_mem

#check (@CoveringDesigns.SaturatedMatching.Remaining.index_ne : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P),
  (∀ (f : M), CoveringDesigns.indexedSubsetDegree B {P.point (f, true), P.point (f, false)} = 2) →
    ∀ (f : M), R.index (f, true) ≠ R.index (f, false))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.index_ne
#print axioms CoveringDesigns.SaturatedMatching.Remaining.index_ne

#check (@CoveringDesigns.SaturatedMatching.Remaining.signature_card : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P),
  (∀ (f : M), CoveringDesigns.indexedSubsetDegree B {P.point (f, true), P.point (f, false)} = 2) →
    ∀ (f : M), (R.signature f).card = 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.signature_card
#print axioms CoveringDesigns.SaturatedMatching.Remaining.signature_card

#check (@CoveringDesigns.SaturatedMatching.Remaining.pair_count : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P) (f g : M) (b c : Bool),
  {i ∈ P.free | P.point (f, b) ∈ B i ∧ P.point (g, c) ∈ B i}.card = if R.index (f, b) = R.index (g, c) then 1 else 0)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.pair_count
#print axioms CoveringDesigns.SaturatedMatching.Remaining.pair_count

#check (@CoveringDesigns.SaturatedMatching.Remaining.four_pair_count : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι]
  [inst_4 : DecidableEq M] {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P) (e h f g : M) (b c : Bool),
  f ≠ g →
    e ≠ h →
      Finset.univ \ {f, g} = {e, h} →
        CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)} =
          ((2 + if (b == P.sign e f) = (c == P.sign e g) then 1 else 0) +
              if (b == P.sign h f) = (c == P.sign h g) then 1 else 0) +
            if R.index (f, b) = R.index (g, c) then 1 else 0)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.four_pair_count
#print axioms CoveringDesigns.SaturatedMatching.Remaining.four_pair_count

#check (@CoveringDesigns.SaturatedMatching.Remaining.equal_of_missing : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι]
  [inst_4 : DecidableEq M] {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P) (e h f g : M) (b c : Bool),
  f ≠ g →
    e ≠ h →
      Finset.univ \ {f, g} = {e, h} →
        (b == P.sign e f) ≠ (c == P.sign e g) →
          (b == P.sign h f) ≠ (c == P.sign h g) →
            3 ≤ CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)} → R.index (f, b) = R.index (g, c))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.equal_of_missing
#print axioms CoveringDesigns.SaturatedMatching.Remaining.equal_of_missing

#check (@CoveringDesigns.SaturatedMatching.Remaining.ne_of_mixed : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [inst_4 : DecidableEq M]
  {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P) (e h f g : M) (b c : Bool),
  f ≠ g →
    e ≠ h →
      Finset.univ \ {f, g} = {e, h} →
        (b == P.sign e f) ≠ (c == P.sign e g) →
          (b == P.sign h f) = (c == P.sign h g) →
            CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)} = 3 → R.index (f, b) ≠ R.index (g, c))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.ne_of_mixed
#print axioms CoveringDesigns.SaturatedMatching.Remaining.ne_of_mixed

#check (@CoveringDesigns.SaturatedMatching.Remaining.signatures_equal_or_disjoint : ∀ {α : Type u_1} {ι : Type u_2}
  {M : Type u_3} [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι]
  [inst_4 : DecidableEq M] {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P) (e h f g : M),
  f ≠ g →
    e ≠ h →
      Finset.univ \ {f, g} = {e, h} →
        (∀ (b c : Bool), 3 ≤ CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)}) →
          (∀ (b c : Bool),
              (b == P.sign e f) ≠ (c == P.sign e g) ∨ (b == P.sign h f) ≠ (c == P.sign h g) →
                CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)} = 3) →
            R.signature f = R.signature g ∨ Disjoint (R.signature f) (R.signature g))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.signatures_equal_or_disjoint
#print axioms CoveringDesigns.SaturatedMatching.Remaining.signatures_equal_or_disjoint

#check (@CoveringDesigns.SaturatedMatching.Remaining.flip_correlation : ∀ (b c u v : Bool),
  ((!b) == u) = (c == v) ↔ ¬(b == u) = (c == v))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.flip_correlation
#print axioms CoveringDesigns.SaturatedMatching.Remaining.flip_correlation

#check (@CoveringDesigns.SaturatedMatching.Remaining.shared_free_separated : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι]
  [inst_4 : DecidableEq M] {B : ι → Finset α} {P : CoveringDesigns.SaturatedMatching.Pattern B}
  (R : CoveringDesigns.SaturatedMatching.Remaining P) (e h f g : M) (b c : Bool),
  f ≠ g →
    e ≠ h →
      Finset.univ \ {f, g} = {e, h} →
        (∀ (f : M), CoveringDesigns.indexedSubsetDegree B {P.point (f, true), P.point (f, false)} = 2) →
          (∀ (b c : Bool), 3 ≤ CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)}) →
            (∀ (b c : Bool),
                (b == P.sign e f) ≠ (c == P.sign e g) ∨ (b == P.sign h f) ≠ (c == P.sign h g) →
                  CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)} = 3) →
              R.index (f, b) = R.index (g, c) → (b == P.sign e f) ≠ (c == P.sign e g))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.shared_free_separated
#print axioms CoveringDesigns.SaturatedMatching.Remaining.shared_free_separated

#check (@CoveringDesigns.SaturatedMatching.saturated_partner_of_mem : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {k : ℕ} {C : CoveringDesigns.Family α} {p q : α} {B : Finset α},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        p ≠ q →
          CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
            B ∈ C → p ∈ B → q ∈ B → ∃ D ∈ C, D ≠ B ∧ B ∪ D = Finset.univ ∧ B ∩ D = {p, q})
#guard_standard_axioms CoveringDesigns.SaturatedMatching.saturated_partner_of_mem
#print axioms CoveringDesigns.SaturatedMatching.saturated_partner_of_mem

#check (@CoveringDesigns.SaturatedMatching.second_partner_block : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {k : ℕ} {C : CoveringDesigns.Family α} {p q z : α} {B D : Finset α},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        p ≠ q →
          B ∈ C →
            B ∪ D = Finset.univ →
              B ∩ D = {p, q} →
                z ∈ B \ {p, q} →
                  CoveringDesigns.degree (CoveringDesigns.star C q) z = 2 →
                    D \ {p, q} ∪ {q, z} ∈ CoveringDesigns.C20_11_3.onlyBlocks C q p)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.second_partner_block
#print axioms CoveringDesigns.SaturatedMatching.second_partner_block

#check (@CoveringDesigns.SaturatedMatching.second_partner_traces_left : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {k : ℕ} {C : CoveringDesigns.Family α} {p q z : α} {B D : Finset α},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        p ≠ q →
          B ∈ C →
            D ∈ C →
              B ∪ D = Finset.univ →
                B ∩ D = {p, q} →
                  z ∈ B \ {p, q} →
                    CoveringDesigns.degree (CoveringDesigns.star C q) z = 2 →
                      ∃ E ∈ CoveringDesigns.C20_11_3.onlyBlocks C q p,
                        (B \ {p, q} ∩ E).card = 1 ∧ (D \ {p, q} ∩ E).card = k - 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.second_partner_traces_left
#print axioms CoveringDesigns.SaturatedMatching.second_partner_traces_left

#check (@CoveringDesigns.SaturatedMatching.second_partner_trace : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {k : ℕ} {C : CoveringDesigns.Family α} {p q z : α} {B D : Finset α},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        p ≠ q →
          B ∈ C →
            D ∈ C →
              B ∪ D = Finset.univ →
                B ∩ D = {p, q} →
                  z ∈ B \ {p, q} ∪ D \ {p, q} →
                    CoveringDesigns.degree (CoveringDesigns.star C q) z = 2 →
                      ∃ E ∈ CoveringDesigns.C20_11_3.onlyBlocks C q p,
                        (B \ {p, q} ∩ E).card * (D \ {p, q} ∩ E).card = k - 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.second_partner_trace
#print axioms CoveringDesigns.SaturatedMatching.second_partner_trace

#check (@CoveringDesigns.SaturatedMatching.intersection_le_pred : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α] {k : ℕ}
  {p : α} {A E : Finset α}, A.card = k → p ∈ A → p ∉ E → (A ∩ E).card ≤ k - 1)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.intersection_le_pred
#print axioms CoveringDesigns.SaturatedMatching.intersection_le_pred

#check (@CoveringDesigns.SaturatedMatching.shared_intersection_sum : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α] {k : ℕ}
  {C : CoveringDesigns.Family α} {p q : α} {A : Finset α},
  A.card = k →
    p ∈ A →
      q ∉ A →
        (∀ (z : α), z ≠ p → z ≠ q → 2 ≤ CoveringDesigns.degree (CoveringDesigns.C20_11_3.onlyBlocks C q p) z) →
          2 * (k - 1) ≤ ∑ E ∈ CoveringDesigns.C20_11_3.onlyBlocks C q p, (A ∩ E).card)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.shared_intersection_sum
#print axioms CoveringDesigns.SaturatedMatching.shared_intersection_sum

#check (@CoveringDesigns.SaturatedMatching.Pattern.named_card : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [Fintype ι] [inst : Fintype M] [DecidableEq α] [inst_2 : DecidableEq ι] [DecidableEq M] {B : ι → Finset α}
  (P : CoveringDesigns.SaturatedMatching.Pattern B), P.named.card = 2 * Fintype.card M)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.named_card
#print axioms CoveringDesigns.SaturatedMatching.Pattern.named_card

#check (@CoveringDesigns.SaturatedMatching.Pattern.free_card : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M] {B : ι → Finset α}
  (P : CoveringDesigns.SaturatedMatching.Pattern B), P.free.card + 2 * Fintype.card M = Fintype.card ι)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.free_card
#print axioms CoveringDesigns.SaturatedMatching.Pattern.free_card

#check (@CoveringDesigns.SaturatedMatching.Pattern.sum_partition : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M] {B : ι → Finset α}
  (P : CoveringDesigns.SaturatedMatching.Pattern B) (w : ι → ℕ),
  ∑ i : ι, w i = ∑ e : M, (w (P.block (e, true)) + w (P.block (e, false))) + ∑ i ∈ P.free, w i)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.sum_partition
#print axioms CoveringDesigns.SaturatedMatching.Pattern.sum_partition

#check (@CoveringDesigns.SaturatedMatching.Pattern.degree_named : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [Fintype ι] [inst : Fintype M] [inst_1 : DecidableEq α] [DecidableEq ι] [DecidableEq M] {B : ι → Finset α}
  (P : CoveringDesigns.SaturatedMatching.Pattern B) (f : M) (b : Bool),
  ∑ e : M,
      ((if P.point (f, b) ∈ B (P.block (e, true)) then 1 else 0) +
        if P.point (f, b) ∈ B (P.block (e, false)) then 1 else 0) =
    Fintype.card M + 1)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.degree_named
#print axioms CoveringDesigns.SaturatedMatching.Pattern.degree_named

#check (@CoveringDesigns.SaturatedMatching.Pattern.endpoint_degree : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B) (f : M) (b : Bool),
  CoveringDesigns.indexedDegree B (P.point (f, b)) = Fintype.card M + 1 + {i ∈ P.free | P.point (f, b) ∈ B i}.card)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.endpoint_degree
#print axioms CoveringDesigns.SaturatedMatching.Pattern.endpoint_degree

#check (@CoveringDesigns.SaturatedMatching.Pattern.five_no_free : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B),
  Fintype.card M = 5 →
    (∀ (f : M) (b : Bool), CoveringDesigns.indexedDegree B (P.point (f, b)) = 6) →
      ∀ i ∈ P.free, ∀ (f : M) (b : Bool), P.point (f, b) ∉ B i)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.five_no_free
#print axioms CoveringDesigns.SaturatedMatching.Pattern.five_no_free

#check (@CoveringDesigns.SaturatedMatching.Pattern.four_unique_free : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [DecidableEq M]
  {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B),
  Fintype.card M = 4 →
    (∀ (f : M) (b : Bool), CoveringDesigns.indexedDegree B (P.point (f, b)) = 6) →
      ∀ (f : M) (b : Bool), ∃ i ∈ P.free, ∀ j ∈ P.free, P.point (f, b) ∈ B j ↔ j = i)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.four_unique_free
#print axioms CoveringDesigns.SaturatedMatching.Pattern.four_unique_free

#check (@CoveringDesigns.SaturatedMatching.Pattern.cross_named_contribution : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [Fintype ι] [Fintype M] [inst : DecidableEq α] [DecidableEq ι] [DecidableEq M] {B : ι → Finset α}
  (P : CoveringDesigns.SaturatedMatching.Pattern B) (e f g : M) (b c : Bool),
  e ≠ f →
    e ≠ g →
      ((if P.point (f, b) ∈ B (P.block (e, true)) ∧ P.point (g, c) ∈ B (P.block (e, true)) then 1 else 0) +
          if P.point (f, b) ∈ B (P.block (e, false)) ∧ P.point (g, c) ∈ B (P.block (e, false)) then 1 else 0) =
        if (b == P.sign e f) = (c == P.sign e g) then 1 else 0)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.cross_named_contribution
#print axioms CoveringDesigns.SaturatedMatching.Pattern.cross_named_contribution

#check (@CoveringDesigns.SaturatedMatching.Pattern.own_named_contribution : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [Fintype ι] [Fintype M] [inst : DecidableEq α] [DecidableEq ι] [DecidableEq M] {B : ι → Finset α}
  (P : CoveringDesigns.SaturatedMatching.Pattern B) (f g : M) (b c : Bool),
  f ≠ g →
    ((if P.point (f, b) ∈ B (P.block (f, true)) ∧ P.point (g, c) ∈ B (P.block (f, true)) then 1 else 0) +
        if P.point (f, b) ∈ B (P.block (f, false)) ∧ P.point (g, c) ∈ B (P.block (f, false)) then 1 else 0) =
      1)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.own_named_contribution
#print axioms CoveringDesigns.SaturatedMatching.Pattern.own_named_contribution

#check (@CoveringDesigns.SaturatedMatching.Pattern.pair_partition : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι] [inst_4 : DecidableEq M]
  {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B) (f g : M) (b c : Bool),
  f ≠ g →
    CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)} =
      (2 + ∑ e ∈ Finset.univ \ {f, g}, if (b == P.sign e f) = (c == P.sign e g) then 1 else 0) +
        {i ∈ P.free | P.point (f, b) ∈ B i ∧ P.point (g, c) ∈ B i}.card)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.pair_partition
#print axioms CoveringDesigns.SaturatedMatching.Pattern.pair_partition

#check (@CoveringDesigns.SaturatedMatching.Pattern.five_pair_multiplicity : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  [Fintype α] [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [DecidableEq ι] [inst_4 : DecidableEq M]
  {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B),
  Fintype.card M = 5 →
    (∀ (f : M) (b : Bool), CoveringDesigns.indexedDegree B (P.point (f, b)) = 6) →
      ∀ (f g : M) (b c : Bool),
        f ≠ g →
          CoveringDesigns.indexedSubsetDegree B {P.point (f, b), P.point (g, c)} =
            2 + ∑ e ∈ Finset.univ \ {f, g}, if (b == P.sign e f) = (c == P.sign e g) then 1 else 0)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.five_pair_multiplicity
#print axioms CoveringDesigns.SaturatedMatching.Pattern.five_pair_multiplicity

#check (@CoveringDesigns.SaturatedMatching.Pattern.four_named_lower : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} [Fintype α]
  [inst : Fintype ι] [inst_1 : Fintype M] [inst_2 : DecidableEq α] [DecidableEq ι] [DecidableEq M] {B : ι → Finset α}
  (P : CoveringDesigns.SaturatedMatching.Pattern B),
  Fintype.card M = 4 →
    (∀ (f : M) (b : Bool), CoveringDesigns.indexedDegree B (P.point (f, b)) = 6) →
      ∀ (f : M) (b : Bool) (x : α),
        3 ≤ CoveringDesigns.indexedSubsetDegree B {x, P.point (f, b)} →
          2 ≤
            ∑ e : M,
              ((if x ∈ B (P.block (e, true)) ∧ P.point (f, b) ∈ B (P.block (e, true)) then 1 else 0) +
                if x ∈ B (P.block (e, false)) ∧ P.point (f, b) ∈ B (P.block (e, false)) then 1 else 0))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.four_named_lower
#print axioms CoveringDesigns.SaturatedMatching.Pattern.four_named_lower

#check (@CoveringDesigns.SaturatedMatching.Pattern.relabel_degree : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  {N : Type u_4} [Fintype α] [inst : Fintype ι] [Fintype M] [Fintype N] [inst_3 : DecidableEq α] [DecidableEq ι]
  [DecidableEq M] [inst_6 : DecidableEq N] {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B)
  (r : N ≃ M) (p q : N → Bool),
  (∀ (f : M) (b : Bool), CoveringDesigns.indexedDegree B (P.point (f, b)) = 6) →
    ∀ (f : N) (b : Bool), CoveringDesigns.indexedDegree B ((P.relabel r p q).point (f, b)) = 6)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.relabel_degree
#print axioms CoveringDesigns.SaturatedMatching.Pattern.relabel_degree

#check (@CoveringDesigns.SaturatedMatching.Pattern.relabel_pair_floor : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  {N : Type u_4} [Fintype α] [inst : Fintype ι] [Fintype M] [Fintype N] [inst_3 : DecidableEq α] [DecidableEq ι]
  [DecidableEq M] [inst_6 : DecidableEq N] {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B)
  (r : N ≃ M) (p q : N → Bool),
  (∀ (x : α) (f : M) (b : Bool),
      x ≠ P.point (f, b) → x ≠ P.point (f, !b) → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x, P.point (f, b)}) →
    ∀ (x : α) (f : N) (b : Bool),
      x ≠ (P.relabel r p q).point (f, b) →
        x ≠ (P.relabel r p q).point (f, !b) →
          3 ≤ CoveringDesigns.indexedSubsetDegree B {x, (P.relabel r p q).point (f, b)})
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.relabel_pair_floor
#print axioms CoveringDesigns.SaturatedMatching.Pattern.relabel_pair_floor

#check (@CoveringDesigns.SaturatedMatching.Pattern.relabel_named : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3} {N : Type u_4}
  [Fintype α] [Fintype ι] [inst : Fintype M] [inst_1 : Fintype N] [inst_2 : DecidableEq α] [inst_3 : DecidableEq ι]
  [DecidableEq M] [inst_5 : DecidableEq N] {B : ι → Finset α} (P : CoveringDesigns.SaturatedMatching.Pattern B)
  (r : N ≃ M) (p q : N → Bool), (P.relabel r p q).named = P.named)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Pattern.relabel_named
#print axioms CoveringDesigns.SaturatedMatching.Pattern.relabel_named

#check (@CoveringDesigns.SaturatedMatching.Remaining.relabel_signature : ∀ {α : Type u_1} {ι : Type u_2} {M : Type u_3}
  {N : Type u_4} [inst : Fintype α] [inst_1 : Fintype ι] [inst_2 : Fintype M] [inst_3 : Fintype N]
  [inst_4 : DecidableEq α] [inst_5 : DecidableEq ι] [inst_6 : DecidableEq M] [inst_7 : DecidableEq N] {B : ι → Finset α}
  {P : CoveringDesigns.SaturatedMatching.Pattern B} (R : CoveringDesigns.SaturatedMatching.Remaining P) (r : N ≃ M)
  (p q : N → Bool) (f : N), (R.relabel r p q).signature f = R.signature ((r : N → M) f))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Remaining.relabel_signature
#print axioms CoveringDesigns.SaturatedMatching.Remaining.relabel_signature

#check (@CoveringDesigns.SaturatedMatching.saturated_matching : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α},
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        p ≠ q →
          CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
            ∀ (z : α), z ≠ q → CoveringDesigns.degree (CoveringDesigns.star C q) z = 2 → z = p)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.saturated_matching
#print axioms CoveringDesigns.SaturatedMatching.saturated_matching

#check (@CoveringDesigns.SaturatedMatching.Split.loss_le_five : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 → CoveringDesigns.IsCover C 31 3 → Finset.card C = 13 → s.loss ≤ 5)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.loss_le_five
#print axioms CoveringDesigns.SaturatedMatching.Split.loss_le_five

#check (@CoveringDesigns.SaturatedMatching.Split.no_internal_left : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        ∀ {x y : α}, x ∈ s.X → y ∈ s.X → x ≠ y → CoveringDesigns.degree (CoveringDesigns.star C x) y ≠ 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.no_internal_left
#print axioms CoveringDesigns.SaturatedMatching.Split.no_internal_left

#check (@CoveringDesigns.SaturatedMatching.Split.separates : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        ∀ {x y : α},
          x ≠ p ∧ x ≠ q →
            y ≠ p ∧ y ≠ q →
              x ≠ y → CoveringDesigns.degree (CoveringDesigns.star C x) y = 2 → x ∈ s.X ∧ y ∈ s.Y ∨ x ∈ s.Y ∧ y ∈ s.X)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.separates
#print axioms CoveringDesigns.SaturatedMatching.Split.separates

#check (@CoveringDesigns.SaturatedMatching.Split.no_shared_support : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α}
  (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        ∀ {x y : α},
          x ≠ p ∧ x ≠ q →
            y ≠ p ∧ y ≠ q →
              x ≠ y →
                CoveringDesigns.degree (CoveringDesigns.star C x) y = 2 →
                  ∀ {A : Finset α}, A ∈ C → p ∈ A → q ∈ A → ¬(x ∈ A ∧ y ∈ A))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.no_shared_support
#print axioms CoveringDesigns.SaturatedMatching.Split.no_shared_support

#check (@CoveringDesigns.SaturatedMatching.Split.cross_disjoint : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 →
        ∀ {z w : α × α}, z ∈ s.crosses → w ∈ s.crosses → z ≠ w → (w.1 ≠ z.1 ∧ w.1 ≠ z.2) ∧ w.2 ≠ z.1 ∧ w.2 ≠ z.2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.cross_disjoint
#print axioms CoveringDesigns.SaturatedMatching.Split.cross_disjoint

#check (@CoveringDesigns.SaturatedMatching.Split.cross_card_le_four : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α}
  (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 → CoveringDesigns.IsCover C 31 3 → Finset.card C = 13 → s.crosses.card ≤ 4)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.cross_card_le_four
#print axioms CoveringDesigns.SaturatedMatching.Split.cross_card_le_four

#check (@CoveringDesigns.SaturatedMatching.Split.small_budget : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} (s : CoveringDesigns.SaturatedMatching.Split C p q 31),
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 → (s.crosses.card = 3 ∨ s.crosses.card = 4) ∧ s.loss + s.excess + 3 = s.crosses.card)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.small_budget
#print axioms CoveringDesigns.SaturatedMatching.Split.small_budget

#check (@CoveringDesigns.SaturatedMatching.Split.exists_of_saturated : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α} {k : ℕ},
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        p ≠ q →
          CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
            Nonempty (CoveringDesigns.SaturatedMatching.Split C p q k))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.exists_of_saturated
#print axioms CoveringDesigns.SaturatedMatching.Split.exists_of_saturated

#check (@CoveringDesigns.SaturatedMatching.Split.saturated : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  CoveringDesigns.degree (CoveringDesigns.star C p) q = 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.saturated
#print axioms CoveringDesigns.SaturatedMatching.Split.saturated

#check (@CoveringDesigns.SaturatedMatching.Split.geometry : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Disjoint s.X s.Y ∧ s.X.card = k - 2 ∧ s.Y.card = k - 2 ∧ s.X ∪ s.Y = Finset.univ \ {p, q})
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.geometry
#print axioms CoveringDesigns.SaturatedMatching.Split.geometry

#check (@CoveringDesigns.SaturatedMatching.Split.weight_left : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  s.weight s.left = 0)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.weight_left
#print axioms CoveringDesigns.SaturatedMatching.Split.weight_left

#check (@CoveringDesigns.SaturatedMatching.Split.weight_right : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  s.weight s.right = 0)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.weight_right
#print axioms CoveringDesigns.SaturatedMatching.Split.weight_right

#check (@CoveringDesigns.SaturatedMatching.Split.cap_P : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k) {A : Finset α},
  A ∈ s.P → s.cap A = CoveringDesigns.TwoKMinusTwo.capacity (k - 1))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.cap_P
#print axioms CoveringDesigns.SaturatedMatching.Split.cap_P

#check (@CoveringDesigns.SaturatedMatching.Split.cap_Q : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k) {A : Finset α},
  A ∈ s.Q → s.cap A = CoveringDesigns.TwoKMinusTwo.capacity (k - 1))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.cap_Q
#print axioms CoveringDesigns.SaturatedMatching.Split.cap_Q

#check (@CoveringDesigns.SaturatedMatching.Split.cap_N : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k) {A : Finset α},
  A ∈ s.N → s.cap A = CoveringDesigns.TwoKMinusTwo.capacity k)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.cap_N
#print axioms CoveringDesigns.SaturatedMatching.Split.cap_N

#check (@CoveringDesigns.SaturatedMatching.Split.capacity_bound : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  CoveringDesigns.IsCover C k 3 → ∀ A ∈ C, s.weight A ≤ s.cap A)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.capacity_bound
#print axioms CoveringDesigns.SaturatedMatching.Split.capacity_bound

#check (@CoveringDesigns.SaturatedMatching.Split.cap_sum : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  ∑ A ∈ C, s.cap A =
    CoveringDesigns.TwoKMinusTwo.capacity (k - 1) * (Finset.card s.P + Finset.card s.Q) +
      CoveringDesigns.TwoKMinusTwo.capacity k * Finset.card s.N)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.cap_sum
#print axioms CoveringDesigns.SaturatedMatching.Split.cap_sum

#check (@CoveringDesigns.SaturatedMatching.Split.parts : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Finset.card C = Finset.card s.P + Finset.card s.Q + Finset.card s.N + 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.parts
#print axioms CoveringDesigns.SaturatedMatching.Split.parts

#check (@CoveringDesigns.SaturatedMatching.Split.assignment : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        ∃ (f : α × α → Finset α × Finset α),
          (∀ z ∈ s.crosses, (f z).1 ∈ s.P ∧ (f z).2 ∈ s.Q ∧ (f z).1 ∩ (f z).2 = {z.1, z.2}) ∧
            Set.InjOn f (↑s.crosses : Set (α × α)))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.assignment
#print axioms CoveringDesigns.SaturatedMatching.Split.assignment

#check (@CoveringDesigns.SaturatedMatching.Split.cross_card_le : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Fintype.card α = 2 * k - 2 →
    3 ≤ k → CoveringDesigns.IsCover C k 3 → s.crosses.card ≤ Finset.card s.P * Finset.card s.Q)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.cross_card_le
#print axioms CoveringDesigns.SaturatedMatching.Split.cross_card_le

#check (@CoveringDesigns.SaturatedMatching.Split.exact_budget : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        s.loss + s.excess + 3 * (k - 2) * (k - 2) =
          CoveringDesigns.TwoKMinusTwo.capacity (k - 1) * (Finset.card s.P + Finset.card s.Q) +
              CoveringDesigns.TwoKMinusTwo.capacity k * Finset.card s.N +
            s.crosses.card)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.exact_budget
#print axioms CoveringDesigns.SaturatedMatching.Split.exact_budget

#check (@CoveringDesigns.SaturatedMatching.Split.loss_at : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  CoveringDesigns.IsCover C k 3 → ∀ {A : Finset α}, A ∈ C → s.cap A - s.weight A ≤ s.loss)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.loss_at
#print axioms CoveringDesigns.SaturatedMatching.Split.loss_at

#check (@CoveringDesigns.SaturatedMatching.Split.residual_degree_two : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {C : CoveringDesigns.Family α} {p q : α} {k : ℕ}
  (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        (∀ (z : α), z ≠ p → z ≠ q → CoveringDesigns.degree (CoveringDesigns.star C q) z ≠ 2) →
          ∀ (z : α), z ≠ p → z ≠ q → 2 ≤ CoveringDesigns.degree s.Q z)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.residual_degree_two
#print axioms CoveringDesigns.SaturatedMatching.Split.residual_degree_two

#check (@CoveringDesigns.SaturatedMatching.Split.refined_bound : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  Fintype.card α = 2 * k - 2 →
    3 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        2 ≤ Finset.card s.Q →
          (∀ (z : α), z ≠ p → z ≠ q → CoveringDesigns.degree (CoveringDesigns.star C q) z ≠ 2) →
            (k - 3) * s.crosses.card ≤ Finset.card s.P * ((Finset.card s.Q - 2) * (k - 1)))
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.refined_bound
#print axioms CoveringDesigns.SaturatedMatching.Split.refined_bound

#check (@CoveringDesigns.SaturatedMatching.Split.swap_P : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k), s.swap.P = s.Q)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.swap_P
#print axioms CoveringDesigns.SaturatedMatching.Split.swap_P

#check (@CoveringDesigns.SaturatedMatching.Split.swap_Q : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k), s.swap.Q = s.P)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.swap_Q
#print axioms CoveringDesigns.SaturatedMatching.Split.swap_Q

#check (@CoveringDesigns.SaturatedMatching.Split.swap_crosses : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α} {k : ℕ} (s : CoveringDesigns.SaturatedMatching.Split C p q k),
  s.swap.crosses = s.crosses)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.Split.swap_crosses
#print axioms CoveringDesigns.SaturatedMatching.Split.swap_crosses

#check (@CoveringDesigns.SaturatedMatching.no_saturation_31 : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q : α},
  Fintype.card α = 60 →
    CoveringDesigns.IsCover C 31 3 →
      Finset.card C = 13 → p ≠ q → CoveringDesigns.degree (CoveringDesigns.star C p) q ≠ 2)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.no_saturation_31
#print axioms CoveringDesigns.SaturatedMatching.no_saturation_31

#check (@CoveringDesigns.C60_31_3.no_thirteen : ∀ {α : Type u_1} [inst : Fintype α] {C : CoveringDesigns.Family α},
  Fintype.card α = 60 → CoveringDesigns.IsCover C 31 3 → Finset.card C = 13 → False)
#guard_standard_axioms CoveringDesigns.C60_31_3.no_thirteen
#print axioms CoveringDesigns.C60_31_3.no_thirteen

#check (@CoveringDesigns.C60_31_3.fourteen_le_card : ∀ {α : Type u_1} [inst : Fintype α] {C : CoveringDesigns.Family α},
  Fintype.card α = 60 → CoveringDesigns.IsCover C 31 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C60_31_3.fourteen_le_card
#print axioms CoveringDesigns.C60_31_3.fourteen_le_card

#check (@CoveringDesigns.C60_31_3.attaining : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 60 → ∃ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 31 3 ∧ Finset.card C = 14)
#guard_standard_axioms CoveringDesigns.C60_31_3.attaining
#print axioms CoveringDesigns.C60_31_3.attaining

#check (@CoveringDesigns.C60_31_3.exactness_on : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 60 →
    (∃ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 31 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 31 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C60_31_3.exactness_on
#print axioms CoveringDesigns.C60_31_3.exactness_on

#check (@CoveringDesigns.covering_number_60_31_3 : (∃ (C : CoveringDesigns.Family (Fin 60)),
    CoveringDesigns.IsCover C 31 3 ∧ Finset.card C = 14) ∧
  ∀ (C : CoveringDesigns.Family (Fin 60)), CoveringDesigns.IsCover C 31 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.covering_number_60_31_3
#print axioms CoveringDesigns.covering_number_60_31_3

#check (@CoveringDesigns.SaturatedMatching.family_pair : ∀ {α : Type u_1} [inst : DecidableEq α] (C : CoveringDesigns.Family α)
  (x y : α),
  CoveringDesigns.indexedSubsetDegree (fun (B : ↥C) => (↑B : Finset α)) {x, y} =
    CoveringDesigns.degree (CoveringDesigns.star C x) y)
#guard_standard_axioms CoveringDesigns.SaturatedMatching.family_pair
#print axioms CoveringDesigns.SaturatedMatching.family_pair

#check (@CoveringDesigns.C62_32_3.no_thirteen : ∀ {α : Type u_1} [inst : Fintype α] {C : CoveringDesigns.Family α},
  Fintype.card α = 62 → CoveringDesigns.IsCover C 32 3 → Finset.card C = 13 → False)
#guard_standard_axioms CoveringDesigns.C62_32_3.no_thirteen
#print axioms CoveringDesigns.C62_32_3.no_thirteen

#check (@CoveringDesigns.C62_32_3.fourteen_le_card : ∀ {α : Type u_1} [inst : Fintype α] {C : CoveringDesigns.Family α},
  Fintype.card α = 62 → CoveringDesigns.IsCover C 32 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C62_32_3.fourteen_le_card
#print axioms CoveringDesigns.C62_32_3.fourteen_le_card

#check (@CoveringDesigns.C62_32_3.attaining : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 62 → ∃ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 32 3 ∧ Finset.card C = 14)
#guard_standard_axioms CoveringDesigns.C62_32_3.attaining
#print axioms CoveringDesigns.C62_32_3.attaining

#check (@CoveringDesigns.C62_32_3.exactness_on : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 62 →
    (∃ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 32 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 32 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C62_32_3.exactness_on
#print axioms CoveringDesigns.C62_32_3.exactness_on

#check (@CoveringDesigns.covering_number_62_32_3 : (∃ (C : CoveringDesigns.Family (Fin 62)),
    CoveringDesigns.IsCover C 32 3 ∧ Finset.card C = 14) ∧
  ∀ (C : CoveringDesigns.Family (Fin 62)), CoveringDesigns.IsCover C 32 3 → 14 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.covering_number_62_32_3
#print axioms CoveringDesigns.covering_number_62_32_3

end MatchingContracts

namespace CoveringDesigns.AuditSaturatedMatching
attribute [local instance] Classical.propDecidable

/-- The final ordinary contract expanded into finite sets of distinct blocks. -/
theorem exactness_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 31 ≤ k) :
    (∃ C : Finset (Finset α),
      (∀ B ∈ C, B.card = k) ∧
      (∀ U : Finset α, U.card = 3 → ∃ B ∈ C, U ⊆ B) ∧ C.card = 14) ∧
    (∀ C : Finset (Finset α),
      (∀ B ∈ C, B.card = k) →
      (∀ U : Finset α, U.card = 3 → ∃ B ∈ C, U ⊆ B) → 14 ≤ C.card) := by
  obtain ⟨⟨C,hC,hc⟩,hl⟩ := TwoKMinusTwoMatching.exactness_on hv hk
  exact ⟨⟨C,hC.1,hC.2,hc⟩,fun D hs ht => hl D ⟨hs,ht⟩⟩

#guard_standard_axioms exactness_explicit
#print axioms exactness_explicit
end CoveringDesigns.AuditSaturatedMatching
