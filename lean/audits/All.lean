import CoveringDesigns
#check (CoveringDesigns.lower_bound_20_11_3 :
  ∀ {α : Type} [Fintype α] [DecidableEq α] {C : CoveringDesigns.Family α},
    Fintype.card α = 20 → CoveringDesigns.IsCover C 11 3 → 12 ≤ C.card)

#check (CoveringDesigns.covering_number_20_11_3_on :
  ∀ {α : Type} [Fintype α] [DecidableEq α], Fintype.card α = 20 →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 11 3 ∧ C.card = 12) ∧
    (∀ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 11 3 → 12 ≤ C.card))

#guard_standard_axioms CoveringDesigns.lower_bound_20_11_3
  CoveringDesigns.covering_number_20_11_3_on
  CoveringDesigns.covering_number_20_11_3

#print axioms CoveringDesigns.lower_bound_20_11_3

#print axioms CoveringDesigns.covering_number_20_11_3_on

#print axioms CoveringDesigns.covering_number_20_11_3

#check (CoveringDesigns.Weighted.diagonal_add_posDef_of_weighted_row_sum_lt :
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ c : ι → ℝ) (E : Matrix ι ι ℝ),
    (∀ i j, E i j = E j i) → (∀ i j, 0 ≤ E i j) → (∀ i, 0 < c i) →
    (∀ i, ∑ j, E i j * c j < ρ i * c i) → (Matrix.diagonal ρ + E).PosDef)

#check (CoveringDesigns.Weighted.gram_card_le_of_weighted_row_sum_lt :
  ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (X : Matrix ι κ ℝ) (ρ c : ι → ℝ) (E P : Matrix ι ι ℝ),
    (∀ i j, E i j = E j i) → (∀ i j, 0 ≤ E i j) → (∀ i, 0 < c i) →
    (∀ i, ∑ j, E i j * c j < ρ i * c i) → P.PosSemidef →
    X * X.transpose = Matrix.diagonal ρ + E + P → Fintype.card ι ≤ Fintype.card κ)

#check (CoveringDesigns.Weighted.two_level_ceiling :
  ∀ {ι : Type*} (S : Finset ι) (u : ι → ℕ) {m K b : ℕ} {α β : ℝ},
    0 ≤ β → 2*β ≤ α → (∀ x ∈ S, m ≤ u x) → (∑ x ∈ S, u x) = K*b →
    α * (S.filter (fun x => u x=m)).card + β * (S.filter (fun x => u x=m+1)).card ≤ b →
    ⌈(S.card : ℝ)*((m : ℝ)*(α-β)+α)/((K : ℝ)*(α-β)+1)⌉₊ ≤ b)

#guard_standard_axioms CoveringDesigns.Weighted.diagonal_add_posDef_of_weighted_row_sum_lt
  CoveringDesigns.Weighted.gram_card_le_of_weighted_row_sum_lt
  CoveringDesigns.Weighted.two_level_ceiling

#print axioms CoveringDesigns.Weighted.diagonal_add_posDef_of_weighted_row_sum_lt

#print axioms CoveringDesigns.Weighted.gram_card_le_of_weighted_row_sum_lt

#print axioms CoveringDesigns.Weighted.two_level_ceiling

#print CoveringDesigns.Family

#print CoveringDesigns.Uniform

#print CoveringDesigns.Covers

#print CoveringDesigns.IsCover

#check (CoveringDesigns.covering_number_11_5_2 :
  (∃ C : Finset (Finset (Fin 11)), CoveringDesigns.IsCover C 5 2 ∧ C.card = 7) ∧
  (∀ C : Finset (Finset (Fin 11)), CoveringDesigns.IsCover C 5 2 → 7 ≤ C.card))

#check (CoveringDesigns.covering_number_12_6_3 :
  (∃ C : Finset (Finset (Fin 12)), CoveringDesigns.IsCover C 6 3 ∧ C.card = 15) ∧
  (∀ C : Finset (Finset (Fin 12)), CoveringDesigns.IsCover C 6 3 → 15 ≤ C.card))

#check (CoveringDesigns.covering_number_13_7_4 :
  (∃ C : Finset (Finset (Fin 13)), CoveringDesigns.IsCover C 7 4 ∧ C.card = 30) ∧
  (∀ C : Finset (Finset (Fin 13)), CoveringDesigns.IsCover C 7 4 → 30 ≤ C.card))

#check (CoveringDesigns.Schoenheim.lower_bound :
  ∀ {α : Type} [Fintype α] [DecidableEq α] {C : CoveringDesigns.Family α} {k t : ℕ},
    1 ≤ t → t ≤ k → k ≤ Fintype.card α → CoveringDesigns.IsCover C k t →
    CoveringDesigns.Schoenheim.bound (Fintype.card α) k t ≤ C.card)

#guard_standard_axioms CoveringDesigns.covering_number_11_5_2
  CoveringDesigns.covering_number_12_6_3
  CoveringDesigns.covering_number_13_7_4
  CoveringDesigns.stanton_classification
  CoveringDesigns.gppt_structural_reduction
  CoveringDesigns.gppt_classification
  CoveringDesigns.Schoenheim.lower_bound

#print axioms CoveringDesigns.covering_number_11_5_2

#print axioms CoveringDesigns.covering_number_12_6_3

#print axioms CoveringDesigns.covering_number_13_7_4

#print axioms CoveringDesigns.stanton_classification

#print axioms CoveringDesigns.gppt_structural_reduction

#print axioms CoveringDesigns.gppt_classification

#print axioms CoveringDesigns.Schoenheim.lower_bound

#check (CoveringDesigns.C17_9_5.lower_bound :
  ∀ {α : Type} [Fintype α] [DecidableEq α] {C : CoveringDesigns.Family α},
    Fintype.card α = 17 → CoveringDesigns.IsCover C 9 5 → 60 ≤ C.card)

#check (CoveringDesigns.C17_9_5.counting_bound :
  ∀ {α : Type} [Fintype α] [DecidableEq α] {C : CoveringDesigns.Family α},
    Fintype.card α = 17 → CoveringDesigns.IsCover C 9 5 →
      (15368 : ℤ) ≤ 260*C.card)

#guard_standard_axioms CoveringDesigns.C17_9_5.lower_bound
  CoveringDesigns.C17_9_5.counting_bound
  CoveringDesigns.WeightedPartition.exists_balanced_partition
  CoveringDesigns.Applications.ZeroDefect.zero_defect_rank_bound

#print axioms CoveringDesigns.C17_9_5.lower_bound

#print axioms CoveringDesigns.C17_9_5.counting_bound

#print axioms CoveringDesigns.WeightedPartition.exists_balanced_partition

#print axioms CoveringDesigns.Applications.ZeroDefect.zero_defect_rank_bound

#check (CoveringDesigns.CaroTuza.exists_selection :
  ∀ {α : Type*} {m : ℕ}, 0 < m → ∀ (w : α → α → ℝ) (V : Finset α),
    CoveringDesigns.CaroTuza.GraphOn w V → CoveringDesigns.CaroTuza.UnitEdges m w V →
    ∃ S ⊆ V, (∀ x ∈ S, CoveringDesigns.CaroTuza.degree w S x < m) ∧
      ⌈CoveringDesigns.CaroTuza.potential m w V⌉₊ ≤ S.card)

#guard_standard_axioms CoveringDesigns.CaroTuza.exists_selection
  CoveringDesigns.CaroTuza.exists_nat_selection
  CoveringDesigns.CaroTuza.potential_erase_le

#print axioms CoveringDesigns.CaroTuza.exists_selection

#print axioms CoveringDesigns.CaroTuza.exists_nat_selection

#print axioms CoveringDesigns.CaroTuza.potential_erase_le

universe uSmallDefectB
universe uSmallDefectC
universe uMulticover vMulticover
#check (CoveringDesigns.Multicover.lower_bound :
  ∀ {α : Type uMulticover} {ι : Type vMulticover}
    [Fintype α] [DecidableEq α] [Fintype ι]
    {B : ι → Finset α} {k t lam : ℕ},
    t ≤ k → k ≤ Fintype.card α → CoveringDesigns.Multicover.IsCover B k t lam →
    CoveringDesigns.Multicover.bound lam (Fintype.card α) k t ≤ Fintype.card ι)

#guard_standard_axioms CoveringDesigns.Multicover.lower_bound
  CoveringDesigns.Multicover.subsetLink_multiplicity
  CoveringDesigns.Multicover.multiset_lower_bound

#print axioms CoveringDesigns.Multicover.lower_bound

#print axioms CoveringDesigns.Multicover.subsetLink_multiplicity

#print axioms CoveringDesigns.Multicover.multiset_lower_bound

universe uMulticoverIncidence wMulticoverIncidence
universe uMulticoverLargeDefect wMulticoverLargeDefect
#check (CoveringDesigns.MulticoverLargeDefect.lower_bound :
  ∀ {α : Type uMulticoverLargeDefect} {ι : Type wMulticoverLargeDefect}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    {lam v k t s : ℕ} {b : ℕ → ℕ},
    CoveringDesigns.MulticoverIncidence.Parameters lam v k t s b →
    CoveringDesigns.MulticoverIncidence.SmallerBounds.{uMulticoverLargeDefect,wMulticoverLargeDefect}
      lam v k t s b →
    Fintype.card α=v → CoveringDesigns.Multicover.IsCover B k t lam → b s < k.choose s →
    1 ≤ CoveringDesigns.HigherIncidence.coefficient s b s →
    CoveringDesigns.HigherIncidence.coefficient s b s ≤ CoveringDesigns.HigherIncidence.defect v k s b →
    CoveringDesigns.MulticoverLargeDefect.bound v k s b ≤ Fintype.card ι)

#guard_standard_axioms CoveringDesigns.MulticoverLargeDefect.lower_bound
  CoveringDesigns.MulticoverLargeDefect.lower_bound_inequality
  CoveringDesigns.MulticoverLargeDefect.selection_bound

#print axioms CoveringDesigns.MulticoverLargeDefect.lower_bound

#print axioms CoveringDesigns.MulticoverLargeDefect.lower_bound_inequality

#print axioms CoveringDesigns.MulticoverLargeDefect.selection_bound

namespace CoveringDesigns.AuditPointReduction
open Finset PointReduction
universe u v w
#check (CoveringDesigns.PointReduction.reduce_points : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype α] [Fintype ι] {B : ι → Finset α} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hk : k ≤ Fintype.card β)
    (hv : Fintype.card β ≤ Fintype.card α),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam)

#check (CoveringDesigns.PointReduction.reduce_along : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype ι] (e : β ↪ α) {B : ι → Finset α} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hk : k ≤ Fintype.card β),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam ∧
      (∀ i, pullback e (B i) ⊆ B' i) ∧
      ∀ T : Finset β, indexedSubsetDegree B (T.map e) ≤ indexedSubsetDegree B' T)

#check (CoveringDesigns.PointReduction.multiplicity_le : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype ι] (e : β ↪ α) (B : ι → Finset α)
    (B' : ι → Finset β) (hp : ∀ i, pullback e (B i) ⊆ B' i) (T : Finset β),
  indexedSubsetDegree B (T.map e) ≤ indexedSubsetDegree B' T)

#check (CoveringDesigns.PointReduction.coverLower_mono : ∀ {v₀ v₁ k t lam L : ℕ}
    (hk : k ≤ v₀) (hv : v₀ ≤ v₁)
    (hl : Multicover.CoverLower.{u,w} v₀ k t lam L),
  Multicover.CoverLower.{u,w} v₁ k t lam L)

#check (CoveringDesigns.PointReduction.exists_cover_le : ∀ {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {k t lam b : ℕ} (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α)
    (h : ∃ B : ι → Finset α, Multicover.IsCover B k t lam ∧ Fintype.card ι ≤ b),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam ∧ Fintype.card ι ≤ b)

#check (CoveringDesigns.PointReduction.exists_cover_exact : ∀ {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {k t lam b : ℕ} (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α)
    (h : ∃ B : ι → Finset α, Multicover.IsCover B k t lam ∧ Fintype.card ι=b),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam ∧ Fintype.card ι=b)

#check (CoveringDesigns.PointReduction.family_reduce_points : ∀ {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {C : Family α} {k t : ℕ} (h : IsCover C k t)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α),
  ∃ D : Family β, IsCover D k t ∧ D.card ≤ C.card)

#check (CoveringDesigns.PointReduction.family_lower_mono : ∀ {v₀ v₁ k t L : ℕ} (hk : k ≤ v₀) (hv : v₀ ≤ v₁)
    (hl : ∀ {β : Type u} [Fintype β] [DecidableEq β] {D : Family β},
      Fintype.card β=v₀ → IsCover D k t → L ≤ D.card)
    {α : Type u} [Fintype α] [DecidableEq α] {C : Family α}
    (hn : Fintype.card α=v₁) (h : IsCover C k t),
  L ≤ C.card)

#check (CoveringDesigns.PointReduction.reduce_points_explicit : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype α] [Fintype ι]
    {B : ι → Finset α} {k t lam : ℕ}
    (hu : ∀ i, (B i).card=k)
    (hc : ∀ T : Finset α, T.card=t → lam ≤ (univ.filter (fun i => T ⊆ B i)).card)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α),
  ∃ B' : ι → Finset β, (∀ i, (B' i).card=k) ∧
      ∀ T : Finset β, T.card=t → lam ≤ (univ.filter (fun i => T ⊆ B' i)).card)

end CoveringDesigns.AuditPointReduction

#guard_standard_axioms CoveringDesigns.PointReduction.reduce_points
  CoveringDesigns.PointReduction.reduce_along
  CoveringDesigns.PointReduction.multiplicity_le
  CoveringDesigns.PointReduction.coverLower_mono
  CoveringDesigns.PointReduction.exists_cover_le
  CoveringDesigns.PointReduction.exists_cover_exact
  CoveringDesigns.PointReduction.family_reduce_points
  CoveringDesigns.PointReduction.family_lower_mono
  CoveringDesigns.PointReduction.reduce_points_explicit

#print axioms CoveringDesigns.PointReduction.reduce_points

#print axioms CoveringDesigns.PointReduction.reduce_along

#print axioms CoveringDesigns.PointReduction.multiplicity_le

#print axioms CoveringDesigns.PointReduction.coverLower_mono

#print axioms CoveringDesigns.PointReduction.exists_cover_le

#print axioms CoveringDesigns.PointReduction.exists_cover_exact

#print axioms CoveringDesigns.PointReduction.family_reduce_points

#print axioms CoveringDesigns.PointReduction.family_lower_mono

#print axioms CoveringDesigns.PointReduction.reduce_points_explicit

#check CoveringDesigns.TwoKMinusTwo.conditional_rank

#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.conditional_rank

#print axioms CoveringDesigns.TwoKMinusTwo.conditional_rank

#check CoveringDesigns.TwoKMinusTwo.saturated_capacity

#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.saturated_capacity

#print axioms CoveringDesigns.TwoKMinusTwo.saturated_capacity

#check CoveringDesigns.TwoKMinusTwo.lower_inequality

#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.lower_inequality

#print axioms CoveringDesigns.TwoKMinusTwo.lower_inequality

#check CoveringDesigns.TwoKMinusTwo.thirteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.thirteen_le_card

#print axioms CoveringDesigns.TwoKMinusTwo.thirteen_le_card

#check CoveringDesigns.TwoKMinusTwo.fourteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.fourteen_le_card

#print axioms CoveringDesigns.TwoKMinusTwo.fourteen_le_card

#check CoveringDesigns.TwoKMinusTwo.upper_bound

#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.upper_bound

#print axioms CoveringDesigns.TwoKMinusTwo.upper_bound

#check CoveringDesigns.TwoKMinusTwo.exactness

#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.exactness

#print axioms CoveringDesigns.TwoKMinusTwo.exactness

#check CoveringDesigns.TwoKMinusTwo.covering_number

#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.covering_number

#print axioms CoveringDesigns.TwoKMinusTwo.covering_number

#check CoveringDesigns.BoundaryRank.component_pairing

#guard_standard_axioms CoveringDesigns.BoundaryRank.component_pairing

#print axioms CoveringDesigns.BoundaryRank.component_pairing

#check CoveringDesigns.BoundaryRank.gram_equality

#guard_standard_axioms CoveringDesigns.BoundaryRank.gram_equality

#print axioms CoveringDesigns.BoundaryRank.gram_equality

#check CoveringDesigns.TwoKMinusTwoEquality.constant_posSemidef

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.constant_posSemidef

#print axioms CoveringDesigns.TwoKMinusTwoEquality.constant_posSemidef

#check CoveringDesigns.TwoKMinusTwoEquality.rows_eq_of_gram

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.rows_eq_of_gram

#print axioms CoveringDesigns.TwoKMinusTwoEquality.rows_eq_of_gram

#check CoveringDesigns.TwoKMinusTwoEquality.square_parameters

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.square_parameters

#print axioms CoveringDesigns.TwoKMinusTwoEquality.square_parameters

#check CoveringDesigns.TwoKMinusTwoEquality.boundary_parameter

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.boundary_parameter

#print axioms CoveringDesigns.TwoKMinusTwoEquality.boundary_parameter

#check CoveringDesigns.TwoKMinusTwoEquality.low_row_sum

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.low_row_sum

#print axioms CoveringDesigns.TwoKMinusTwoEquality.low_row_sum

#check CoveringDesigns.TwoKMinusTwoEquality.low_equality_rigidity

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.low_equality_rigidity

#print axioms CoveringDesigns.TwoKMinusTwoEquality.low_equality_rigidity

#check CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_low_equality

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_low_equality

#print axioms CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_low_equality

#check CoveringDesigns.TwoKMinusTwoEquality.low_count_eq_of_tight

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.low_count_eq_of_tight

#print axioms CoveringDesigns.TwoKMinusTwoEquality.low_count_eq_of_tight

#check CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_tight

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_tight

#print axioms CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_tight

#check CoveringDesigns.TwoKMinusTwoEquality.lower_bound_36_19_3

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.lower_bound_36_19_3

#print axioms CoveringDesigns.TwoKMinusTwoEquality.lower_bound_36_19_3

#check CoveringDesigns.TwoKMinusTwoEquality.lower_bound_78_40_3

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.lower_bound_78_40_3

#print axioms CoveringDesigns.TwoKMinusTwoEquality.lower_bound_78_40_3

#check CoveringDesigns.TwoKMinusTwoEquality.thirteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.thirteen_le_card

#print axioms CoveringDesigns.TwoKMinusTwoEquality.thirteen_le_card

#check CoveringDesigns.TwoKMinusTwoEquality.fourteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.fourteen_le_card

#print axioms CoveringDesigns.TwoKMinusTwoEquality.fourteen_le_card

#check CoveringDesigns.TwoKMinusTwoEquality.exactness

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.exactness

#print axioms CoveringDesigns.TwoKMinusTwoEquality.exactness

#check CoveringDesigns.TwoKMinusTwoEquality.covering_number

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.covering_number

#print axioms CoveringDesigns.TwoKMinusTwoEquality.covering_number

#check CoveringDesigns.TwoKMinusTwoEquality.interval_36_19_3_on

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.interval_36_19_3_on

#print axioms CoveringDesigns.TwoKMinusTwoEquality.interval_36_19_3_on

#check CoveringDesigns.TwoKMinusTwoEquality.exactness_78_40_3_on

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoEquality.exactness_78_40_3_on

#print axioms CoveringDesigns.TwoKMinusTwoEquality.exactness_78_40_3_on

#check CoveringDesigns.TwoKMinusC.coefficient_zero

#guard_standard_axioms CoveringDesigns.TwoKMinusC.coefficient_zero

#print axioms CoveringDesigns.TwoKMinusC.coefficient_zero

#check CoveringDesigns.TwoKMinusC.coefficient_one

#guard_standard_axioms CoveringDesigns.TwoKMinusC.coefficient_one

#print axioms CoveringDesigns.TwoKMinusC.coefficient_one

#check CoveringDesigns.TwoKMinusC.defect_eq

#guard_standard_axioms CoveringDesigns.TwoKMinusC.defect_eq

#print axioms CoveringDesigns.TwoKMinusC.defect_eq

#check CoveringDesigns.TwoKMinusC.offsetDefect_ge

#guard_standard_axioms CoveringDesigns.TwoKMinusC.offsetDefect_ge

#print axioms CoveringDesigns.TwoKMinusC.offsetDefect_ge

#check CoveringDesigns.TwoKMinusC.denominator_pos

#guard_standard_axioms CoveringDesigns.TwoKMinusC.denominator_pos

#print axioms CoveringDesigns.TwoKMinusC.denominator_pos

#check CoveringDesigns.TwoKMinusC.value_eq_Q

#guard_standard_axioms CoveringDesigns.TwoKMinusC.value_eq_Q

#print axioms CoveringDesigns.TwoKMinusC.value_eq_Q

#check CoveringDesigns.TwoKMinusC.Q_nonneg

#guard_standard_axioms CoveringDesigns.TwoKMinusC.Q_nonneg

#print axioms CoveringDesigns.TwoKMinusC.Q_nonneg

#check CoveringDesigns.TwoKMinusC.Q_le_iff

#guard_standard_axioms CoveringDesigns.TwoKMinusC.Q_le_iff

#print axioms CoveringDesigns.TwoKMinusC.Q_le_iff

#check CoveringDesigns.TwoKMinusC.ceil_Q_le_iff

#guard_standard_axioms CoveringDesigns.TwoKMinusC.ceil_Q_le_iff

#print axioms CoveringDesigns.TwoKMinusC.ceil_Q_le_iff

#check CoveringDesigns.TwoKMinusC.actual_subset_floors

#guard_standard_axioms CoveringDesigns.TwoKMinusC.actual_subset_floors

#print axioms CoveringDesigns.TwoKMinusC.actual_subset_floors

#check CoveringDesigns.TwoKMinusC.actual_floors_bound

#guard_standard_axioms CoveringDesigns.TwoKMinusC.actual_floors_bound

#print axioms CoveringDesigns.TwoKMinusC.actual_floors_bound

#check CoveringDesigns.TwoKMinusC.actual_floors_real

#guard_standard_axioms CoveringDesigns.TwoKMinusC.actual_floors_real

#print axioms CoveringDesigns.TwoKMinusC.actual_floors_real

#check CoveringDesigns.TwoKMinusC.actual_floors_inequality

#guard_standard_axioms CoveringDesigns.TwoKMinusC.actual_floors_inequality

#print axioms CoveringDesigns.TwoKMinusC.actual_floors_inequality

#check CoveringDesigns.TwoKMinusC.Q_two

#guard_standard_axioms CoveringDesigns.TwoKMinusC.Q_two

#print axioms CoveringDesigns.TwoKMinusC.Q_two

#check CoveringDesigns.TwoKMinusC.twelve_lt_Q_two

#guard_standard_axioms CoveringDesigns.TwoKMinusC.twelve_lt_Q_two

#print axioms CoveringDesigns.TwoKMinusC.twelve_lt_Q_two

#check CoveringDesigns.TwoKMinusC.thirteen_lt_Q_two

#guard_standard_axioms CoveringDesigns.TwoKMinusC.thirteen_lt_Q_two

#print axioms CoveringDesigns.TwoKMinusC.thirteen_lt_Q_two

#check CoveringDesigns.TwoKMinusC.OffsetTwo.thirteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.thirteen_le_card

#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.thirteen_le_card

#check CoveringDesigns.TwoKMinusC.OffsetTwo.fourteen_le_card

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.fourteen_le_card

#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.fourteen_le_card

#check CoveringDesigns.TwoKMinusC.OffsetTwo.exactness

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.exactness

#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.exactness

#check CoveringDesigns.TwoKMinusC.OffsetTwo.covering_number

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.covering_number

#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.covering_number

#check CoveringDesigns.TwoKMinusC.OffsetTwo.interval_34_18_3_on

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.interval_34_18_3_on

#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.interval_34_18_3_on

#check CoveringDesigns.TwoKMinusC.OffsetTwo.exactness_70_36_3_on

#guard_standard_axioms CoveringDesigns.TwoKMinusC.OffsetTwo.exactness_70_36_3_on

#print axioms CoveringDesigns.TwoKMinusC.OffsetTwo.exactness_70_36_3_on

#check CoveringDesigns.Weighted.partitioned_gram_card_le

#guard_standard_axioms CoveringDesigns.Weighted.partitioned_gram_card_le

#print axioms CoveringDesigns.Weighted.partitioned_gram_card_le

#check CoveringDesigns.TwoKMinusCGeneral.link_capacity_strict

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.link_capacity_strict

#print axioms CoveringDesigns.TwoKMinusCGeneral.link_capacity_strict

#check CoveringDesigns.TwoKMinusCGeneral.capacity_uniform_impossible

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.capacity_uniform_impossible

#print axioms CoveringDesigns.TwoKMinusCGeneral.capacity_uniform_impossible

#check CoveringDesigns.TwoKMinusCGeneral.endpoint_budget_three

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.endpoint_budget_three

#print axioms CoveringDesigns.TwoKMinusCGeneral.endpoint_budget_three

#check CoveringDesigns.TwoKMinusCGeneral.capacity_three_impossible

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.capacity_three_impossible

#print axioms CoveringDesigns.TwoKMinusCGeneral.capacity_three_impossible

#check CoveringDesigns.TwoKMinusCGeneral.exists_cross_assignment

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exists_cross_assignment

#print axioms CoveringDesigns.TwoKMinusCGeneral.exists_cross_assignment

#check CoveringDesigns.TwoKMinusCGeneral.saturated_cross_card_le

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.saturated_cross_card_le

#print axioms CoveringDesigns.TwoKMinusCGeneral.saturated_cross_card_le

#check CoveringDesigns.TwoKMinusCGeneral.upper_bound

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.upper_bound

#print axioms CoveringDesigns.TwoKMinusCGeneral.upper_bound

#check CoveringDesigns.TwoKMinusCGeneral.endpoint_trace_capacity

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.endpoint_trace_capacity

#print axioms CoveringDesigns.TwoKMinusCGeneral.endpoint_trace_capacity

#check CoveringDesigns.TwoKMinusCGeneral.saturated_capacity

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.saturated_capacity

#print axioms CoveringDesigns.TwoKMinusCGeneral.saturated_capacity

#check CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_uniform

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_uniform

#print axioms CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_uniform

#check CoveringDesigns.TwoKMinusCGeneral.exactness_uniform

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_uniform

#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_uniform

#check CoveringDesigns.TwoKMinusCGeneral.covering_number_uniform

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.covering_number_uniform

#print axioms CoveringDesigns.TwoKMinusCGeneral.covering_number_uniform

#check CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_offset_three

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_offset_three

#print axioms CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_offset_three

#check CoveringDesigns.TwoKMinusCGeneral.exactness_offset_three

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_offset_three

#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_offset_three

#check CoveringDesigns.TwoKMinusCGeneral.covering_number_offset_three

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.covering_number_offset_three

#print axioms CoveringDesigns.TwoKMinusCGeneral.covering_number_offset_three

#check CoveringDesigns.TwoKMinusCGeneral.exactness_98_50_3_on

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_98_50_3_on

#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_98_50_3_on

#check CoveringDesigns.TwoKMinusCGeneral.exactness_196_100_3_on

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_196_100_3_on

#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_196_100_3_on

#check CoveringDesigns.TwoKMinusCGeneral.exactness_115_59_3_on

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_115_59_3_on

#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_115_59_3_on

#check CoveringDesigns.TwoKMinusCGeneral.saturated_pair_inter_card

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.saturated_pair_inter_card

#print axioms CoveringDesigns.TwoKMinusCGeneral.saturated_pair_inter_card

#check CoveringDesigns.TwoKMinusCGeneral.saturated_pair_blocks

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.saturated_pair_blocks

#print axioms CoveringDesigns.TwoKMinusCGeneral.saturated_pair_blocks

#check CoveringDesigns.TwoKMinusCGeneral.oriented_blocks_unique

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.oriented_blocks_unique

#print axioms CoveringDesigns.TwoKMinusCGeneral.oriented_blocks_unique

#check CoveringDesigns.TwoKMinusCGeneral.cross_partner_exists

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.cross_partner_exists

#print axioms CoveringDesigns.TwoKMinusCGeneral.cross_partner_exists

#check CoveringDesigns.TwoKMinusCGeneral.link_lower_bound

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.link_lower_bound

#print axioms CoveringDesigns.TwoKMinusCGeneral.link_lower_bound

#check CoveringDesigns.TwoKMinusCGeneral.degree_ge_six

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.degree_ge_six

#print axioms CoveringDesigns.TwoKMinusCGeneral.degree_ge_six

#check CoveringDesigns.TwoKMinusCGeneral.pair_ge_two

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.pair_ge_two

#print axioms CoveringDesigns.TwoKMinusCGeneral.pair_ge_two

#check CoveringDesigns.TwoKMinusCGeneral.Q_three

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.Q_three

#print axioms CoveringDesigns.TwoKMinusCGeneral.Q_three

#check CoveringDesigns.TwoKMinusCGeneral.thirteen_lt_Q_three

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.thirteen_lt_Q_three

#print axioms CoveringDesigns.TwoKMinusCGeneral.thirteen_lt_Q_three

#check CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_offset_three

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_offset_three

#print axioms CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_offset_three

#check CoveringDesigns.TwoKMinusCGeneral.integerExcess_cast

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.integerExcess_cast

#print axioms CoveringDesigns.TwoKMinusCGeneral.integerExcess_cast

#check CoveringDesigns.TwoKMinusCGeneral.integerExcess_nonneg

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.integerExcess_nonneg

#print axioms CoveringDesigns.TwoKMinusCGeneral.integerExcess_nonneg

#check CoveringDesigns.TwoKMinusCGeneral.low_row_le

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.low_row_le

#print axioms CoveringDesigns.TwoKMinusCGeneral.low_row_le

#check CoveringDesigns.TwoKMinusCGeneral.low_card_le

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.low_card_le

#print axioms CoveringDesigns.TwoKMinusCGeneral.low_card_le

#check CoveringDesigns.TwoKMinusCGeneral.conditional_rank

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.conditional_rank

#print axioms CoveringDesigns.TwoKMinusCGeneral.conditional_rank

#check CoveringDesigns.TwoKMinusCGeneral.no_saturation_uniform

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.no_saturation_uniform

#print axioms CoveringDesigns.TwoKMinusCGeneral.no_saturation_uniform

#check CoveringDesigns.TwoKMinusCGeneral.no_saturation_offset_three

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.no_saturation_offset_three

#print axioms CoveringDesigns.TwoKMinusCGeneral.no_saturation_offset_three

#check CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_uniform

#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_uniform

#print axioms CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_uniform

#check (CoveringDesigns.TwoKMinusTwoTightening.exactness :
  ∀ {α : Type*} [Fintype α] {k : ℕ}, Fintype.card α = 2*k-2 → 35 ≤ k →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 → 14 ≤ C.card))

#check (CoveringDesigns.TwoKMinusTwoTightening.thirteen_le_card :
  ∀ {α : Type*} [Fintype α] {k : ℕ} {C : CoveringDesigns.Family α},
    Fintype.card α = 2*k-2 → 17 ≤ k → CoveringDesigns.IsCover C k 3 → 13 ≤ C.card)

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoTightening.exactness
  CoveringDesigns.TwoKMinusTwoTightening.thirteen_le_card

#print axioms CoveringDesigns.TwoKMinusTwoTightening.exactness

#print axioms CoveringDesigns.TwoKMinusTwoTightening.thirteen_le_card

#check (CoveringDesigns.TwoKMinusTwoCapacity.indexed_fourteen_le_card :
  ∀ {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] {k : ℕ}
    (B : ι → Finset α), Fintype.card α = 2*k-2 → 33 ≤ k →
    (∀ i, (B i).card = k) →
    (∀ x y, x ≠ y → 3 ≤ CoveringDesigns.indexedSubsetDegree B {x,y}) →
    14 ≤ Fintype.card ι)

#check (CoveringDesigns.TwoKMinusTwoCapacity.exactness :
  ∀ {α : Type*} [Fintype α] {k : ℕ}, Fintype.card α = 2*k-2 → 33 ≤ k →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 → 14 ≤ C.card))

#check (CoveringDesigns.covering_number_64_33_3 :
    (∃ C : CoveringDesigns.Family (Fin 64), CoveringDesigns.IsCover C 33 3 ∧ C.card = 14) ∧
    (∀ C : CoveringDesigns.Family (Fin 64), CoveringDesigns.IsCover C 33 3 → 14 ≤ C.card))

#check (CoveringDesigns.covering_number_66_34_3 :
    (∃ C : CoveringDesigns.Family (Fin 66), CoveringDesigns.IsCover C 34 3 ∧ C.card = 14) ∧
    (∀ C : CoveringDesigns.Family (Fin 66), CoveringDesigns.IsCover C 34 3 → 14 ≤ C.card))

#guard_standard_axioms CoveringDesigns.TwoKMinusTwoCapacity.indexed_fourteen_le_card
  CoveringDesigns.TwoKMinusTwoCapacity.exactness
  CoveringDesigns.covering_number_64_33_3
  CoveringDesigns.covering_number_66_34_3

#print axioms CoveringDesigns.TwoKMinusTwoCapacity.indexed_fourteen_le_card

#print axioms CoveringDesigns.TwoKMinusTwoCapacity.exactness

#print axioms CoveringDesigns.covering_number_64_33_3

#print axioms CoveringDesigns.covering_number_66_34_3

section SaturatedMatchingContracts
universe u_1
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

#check (@CoveringDesigns.covering_number_60_31_3 : (∃ (C : CoveringDesigns.Family (Fin 60)),
    CoveringDesigns.IsCover C 31 3 ∧ Finset.card C = 14) ∧
  ∀ (C : CoveringDesigns.Family (Fin 60)), CoveringDesigns.IsCover C 31 3 → 14 ≤ Finset.card C)

#guard_standard_axioms CoveringDesigns.covering_number_60_31_3

#print axioms CoveringDesigns.covering_number_60_31_3

#check (@CoveringDesigns.covering_number_62_32_3 : (∃ (C : CoveringDesigns.Family (Fin 62)),
    CoveringDesigns.IsCover C 32 3 ∧ Finset.card C = 14) ∧
  ∀ (C : CoveringDesigns.Family (Fin 62)), CoveringDesigns.IsCover C 32 3 → 14 ≤ Finset.card C)

#guard_standard_axioms CoveringDesigns.covering_number_62_32_3

#print axioms CoveringDesigns.covering_number_62_32_3

end SaturatedMatchingContracts

#check (@CoveringDesigns.lower_bound_18_10_3 :
  ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 18 → CoveringDesigns.IsCover C 10 3 → 12 ≤ C.card)

#check (@CoveringDesigns.covering_number_18_10_3_on :
  ∀ {α : Type*} [Fintype α], Fintype.card α = 18 →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 10 3 ∧ C.card = 12) ∧
    (∀ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 10 3 → 12 ≤ C.card))

#check (@CoveringDesigns.indexed_lower_bound_18_10_3 :
  ∀ {α ι : Type*} [Fintype α] [Fintype ι] (B : ι → Finset α),
    Fintype.card α = 18 → (∀ i, (B i).card = 10) →
    (∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) → 12 ≤ Fintype.card ι)

#guard_standard_axioms CoveringDesigns.lower_bound_18_10_3
  CoveringDesigns.covering_number_18_10_3_on
  CoveringDesigns.covering_number_18_10_3
  CoveringDesigns.indexed_lower_bound_18_10_3

#print axioms CoveringDesigns.lower_bound_18_10_3

#print axioms CoveringDesigns.covering_number_18_10_3_on

#print axioms CoveringDesigns.covering_number_18_10_3

#print axioms CoveringDesigns.indexed_lower_bound_18_10_3

section C18103LiftsContracts
universe u
#check (@CoveringDesigns.Applications.C18103Lifts.lower_bound_19_11_4 : ∀ {α : Type u} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 19 → CoveringDesigns.IsCover C 11 4 → 21 ≤ C.card)

#guard_standard_axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_19_11_4

#print axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_19_11_4

#check (@CoveringDesigns.Applications.C18103Lifts.lower_bound_20_12_5 : ∀ {α : Type u} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 20 → CoveringDesigns.IsCover C 12 5 → 35 ≤ C.card)

#guard_standard_axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_20_12_5

#print axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_20_12_5

#check (@CoveringDesigns.Applications.C18103Lifts.lower_bound_21_13_6 : ∀ {α : Type u} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 21 → CoveringDesigns.IsCover C 13 6 → 57 ≤ C.card)

#guard_standard_axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_21_13_6

#print axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_21_13_6

#check (@CoveringDesigns.Applications.C18103Lifts.lower_bound_22_14_7 : ∀ {α : Type u} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 22 → CoveringDesigns.IsCover C 14 7 → 90 ≤ C.card)

#guard_standard_axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_22_14_7

#print axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_22_14_7

#check (@CoveringDesigns.Applications.C18103Lifts.lower_bound_23_15_8 : ∀ {α : Type u} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 23 → CoveringDesigns.IsCover C 15 8 → 138 ≤ C.card)

#guard_standard_axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_23_15_8

#print axioms CoveringDesigns.Applications.C18103Lifts.lower_bound_23_15_8

end C18103LiftsContracts

namespace C1453Contracts
universe u v
#check (@CoveringDesigns.covering_interval_14_5_3_on : ∀ {α : Type u} [Fintype α],
  Fintype.card α = 14 →
  (∀ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 5 3 → 41 ≤ C.card) ∧
  (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 5 3 ∧ C.card = 43))

#guard_standard_axioms CoveringDesigns.covering_interval_14_5_3_on

#print axioms CoveringDesigns.covering_interval_14_5_3_on

#check (@CoveringDesigns.indexed_lower_bound_14_5_3 : ∀ {α : Type u} {ι : Type v}
  [Fintype α] [Fintype ι] (B : ι → Finset α), Fintype.card α = 14 →
  (∀ i, (B i).card = 5) → (∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) → 41 ≤ Fintype.card ι)

#guard_standard_axioms CoveringDesigns.indexed_lower_bound_14_5_3

#print axioms CoveringDesigns.indexed_lower_bound_14_5_3

end C1453Contracts

#check CoveringDesigns.QuadrupleAssembly.assembly_optimal

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.assembly_optimal

#print axioms CoveringDesigns.QuadrupleAssembly.assembly_optimal

#check CoveringDesigns.covering_number_37_4_3

#guard_standard_axioms CoveringDesigns.covering_number_37_4_3

#print axioms CoveringDesigns.covering_number_37_4_3

#check CoveringDesigns.covering_number_49_4_3

#guard_standard_axioms CoveringDesigns.covering_number_49_4_3

#print axioms CoveringDesigns.covering_number_49_4_3

#check CoveringDesigns.covering_number_61_4_3

#guard_standard_axioms CoveringDesigns.covering_number_61_4_3

#print axioms CoveringDesigns.covering_number_61_4_3

#check CoveringDesigns.covering_number_73_4_3

#guard_standard_axioms CoveringDesigns.covering_number_73_4_3

#print axioms CoveringDesigns.covering_number_73_4_3

#check CoveringDesigns.covering_number_85_4_3

#guard_standard_axioms CoveringDesigns.covering_number_85_4_3

#print axioms CoveringDesigns.covering_number_85_4_3

#check CoveringDesigns.covering_number_97_4_3

#guard_standard_axioms CoveringDesigns.covering_number_97_4_3

#print axioms CoveringDesigns.covering_number_97_4_3

namespace QuadrupleFiniteContracts
open CoveringDesigns CoveringDesigns.QuadrupleAssembly
#check (@CoveringDesigns.QuadrupleAssembly.ceilings_13 : Schoenheim.ceilDiv 11 2 = 6 ∧ Schoenheim.ceilDiv (12*6) 3 = 24 ∧ Schoenheim.ceilDiv (13*24) 4 = 78)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.ceilings_13

#print axioms CoveringDesigns.QuadrupleAssembly.ceilings_13

#check (@CoveringDesigns.QuadrupleAssembly.schoenheim_13 : Schoenheim.bound 13 4 3 = 78)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.schoenheim_13

#print axioms CoveringDesigns.QuadrupleAssembly.schoenheim_13

#check (@CoveringDesigns.QuadrupleAssembly.ceilings_25 : Schoenheim.ceilDiv 23 2 = 12 ∧ Schoenheim.ceilDiv (24*12) 3 = 96 ∧ Schoenheim.ceilDiv (25*96) 4 = 600)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.ceilings_25

#print axioms CoveringDesigns.QuadrupleAssembly.ceilings_25

#check (@CoveringDesigns.QuadrupleAssembly.schoenheim_25 : Schoenheim.bound 25 4 3 = 600)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.schoenheim_25

#print axioms CoveringDesigns.QuadrupleAssembly.schoenheim_25

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V25.checked : selectorCoverCheck id 3 WitnessData.V25.rows WitnessData.V25.ownerIndex = true)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.checked

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.checked

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V25.valid : IsCover WitnessData.V25.blocks 4 3)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.valid

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.valid

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V25.size : WitnessData.V25.blocks.card = 600)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.size

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.size

#check (@CoveringDesigns.knownCover78_13_4_3_correspondence : knownCover78_13_4_3 = SeedData.Filling.rows.toFinset)

#guard_standard_axioms CoveringDesigns.knownCover78_13_4_3_correspondence

#print axioms CoveringDesigns.knownCover78_13_4_3_correspondence

#check (@CoveringDesigns.knownCover78_13_4_3_optimal : IsCover knownCover78_13_4_3 4 3 ∧ knownCover78_13_4_3.card = 78)

#guard_standard_axioms CoveringDesigns.knownCover78_13_4_3_optimal

#print axioms CoveringDesigns.knownCover78_13_4_3_optimal

#check (@CoveringDesigns.knownCover78_13_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 13), IsCover (knownCover78_13_4_3_on hv) 4 3 ∧ (knownCover78_13_4_3_on hv).card = 78)

#guard_standard_axioms CoveringDesigns.knownCover78_13_4_3_on_optimal

#print axioms CoveringDesigns.knownCover78_13_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_13_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 13 → IsCover C 4 3 → 78 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_13_4_3

#print axioms CoveringDesigns.lower_bound_13_4_3

#check (@CoveringDesigns.covering_number_13_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 13 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 78) ∧ (∀ C : Family α, IsCover C 4 3 → 78 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_13_4_3_on

#print axioms CoveringDesigns.covering_number_13_4_3_on

#check (@CoveringDesigns.covering_number_13_4_3 : (∃ C : Family (Fin 13), IsCover C 4 3 ∧ C.card = 78) ∧ (∀ C : Family (Fin 13), IsCover C 4 3 → 78 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_13_4_3

#print axioms CoveringDesigns.covering_number_13_4_3

#check (@CoveringDesigns.knownCover600_25_4_3_correspondence : knownCover600_25_4_3 = WitnessData.V25.rows.toFinset)

#guard_standard_axioms CoveringDesigns.knownCover600_25_4_3_correspondence

#print axioms CoveringDesigns.knownCover600_25_4_3_correspondence

#check (@CoveringDesigns.knownCover600_25_4_3_optimal : IsCover knownCover600_25_4_3 4 3 ∧ knownCover600_25_4_3.card = 600)

#guard_standard_axioms CoveringDesigns.knownCover600_25_4_3_optimal

#print axioms CoveringDesigns.knownCover600_25_4_3_optimal

#check (@CoveringDesigns.knownCover600_25_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 25), IsCover (knownCover600_25_4_3_on hv) 4 3 ∧ (knownCover600_25_4_3_on hv).card = 600)

#guard_standard_axioms CoveringDesigns.knownCover600_25_4_3_on_optimal

#print axioms CoveringDesigns.knownCover600_25_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_25_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 25 → IsCover C 4 3 → 600 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_25_4_3

#print axioms CoveringDesigns.lower_bound_25_4_3

#check (@CoveringDesigns.covering_number_25_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 25 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 600) ∧ (∀ C : Family α, IsCover C 4 3 → 600 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_25_4_3_on

#print axioms CoveringDesigns.covering_number_25_4_3_on

#check (@CoveringDesigns.covering_number_25_4_3 : (∃ C : Family (Fin 25), IsCover C 4 3 ∧ C.card = 600) ∧ (∀ C : Family (Fin 25), IsCover C 4 3 → 600 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_25_4_3

#print axioms CoveringDesigns.covering_number_25_4_3

#check (@CoveringDesigns.QuadrupleAssembly.admissible_below_100_iff : ∀ n : ℕ, (4 ≤ n ∧ n < 100 ∧ n % 12 = 1) ↔ (n = 13 ∨ n = 25 ∨ n = 37 ∨ n = 49 ∨ n = 61 ∨ n = 73 ∨ n = 85 ∨ n = 97))

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.admissible_below_100_iff

#print axioms CoveringDesigns.QuadrupleAssembly.admissible_below_100_iff

#check (@CoveringDesigns.QuadrupleAssembly.formula_divisible_below_100 : ∀ {n : ℕ}, 4 ≤ n → n < 100 → n % 12 = 1 → 24 ∣ n * (n-1)^2)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.formula_divisible_below_100

#print axioms CoveringDesigns.QuadrupleAssembly.formula_divisible_below_100

#check (@CoveringDesigns.covering_number_one_mod_twelve_below_100_on : ∀ {α : Type*} [Fintype α] {n : ℕ}, Fintype.card α = n → 4 ≤ n → n < 100 → n % 12 = 1 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = n * (n-1)^2 / 24) ∧ (∀ C : Family α, IsCover C 4 3 → n * (n-1)^2 / 24 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_one_mod_twelve_below_100_on

#print axioms CoveringDesigns.covering_number_one_mod_twelve_below_100_on

#check (@CoveringDesigns.covering_number_one_mod_twelve_below_100 : ∀ {n : ℕ}, 4 ≤ n → n < 100 → n % 12 = 1 → (∃ C : Family (Fin n), IsCover C 4 3 ∧ C.card = n * (n-1)^2 / 24) ∧ (∀ C : Family (Fin n), IsCover C 4 3 → n * (n-1)^2 / 24 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_one_mod_twelve_below_100

#print axioms CoveringDesigns.covering_number_one_mod_twelve_below_100

end QuadrupleFiniteContracts

#check (@CoveringDesigns.covering_number_34_18_3_on : ∀ {α : Type*} [Fintype α],
    Fintype.card α = 34 →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 18 3 ∧ C.card = 13) ∧
    (∀ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 18 3 → 13 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_34_18_3_on

#print axioms CoveringDesigns.covering_number_34_18_3_on

#check (@CoveringDesigns.lower_bound_15_6_4 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 15 → CoveringDesigns.IsCover C 6 4 → 103 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_15_6_4

#print axioms CoveringDesigns.lower_bound_15_6_4

#check (@CoveringDesigns.lower_bound_16_7_5 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 16 → CoveringDesigns.IsCover C 7 5 → 236 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_16_7_5

#print axioms CoveringDesigns.lower_bound_16_7_5

#check (@CoveringDesigns.lower_bound_17_8_6 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 17 → CoveringDesigns.IsCover C 8 6 → 502 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_17_8_6

#print axioms CoveringDesigns.lower_bound_17_8_6

#check (@CoveringDesigns.lower_bound_18_9_7 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 18 → CoveringDesigns.IsCover C 9 7 → 1004 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_18_9_7

#print axioms CoveringDesigns.lower_bound_18_9_7

#check (@CoveringDesigns.lower_bound_19_10_8 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 19 → CoveringDesigns.IsCover C 10 8 → 1908 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_19_10_8

#print axioms CoveringDesigns.lower_bound_19_10_8

#check (@CoveringDesigns.lower_bound_35_19_4 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 35 → CoveringDesigns.IsCover C 19 4 → 24 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_35_19_4

#print axioms CoveringDesigns.lower_bound_35_19_4

#check (@CoveringDesigns.lower_bound_36_20_5 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 36 → CoveringDesigns.IsCover C 20 5 → 44 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_36_20_5

#print axioms CoveringDesigns.lower_bound_36_20_5

#check (@CoveringDesigns.lower_bound_37_21_6 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 37 → CoveringDesigns.IsCover C 21 6 → 78 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_37_21_6

#print axioms CoveringDesigns.lower_bound_37_21_6

#check (@CoveringDesigns.lower_bound_38_22_7 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 38 → CoveringDesigns.IsCover C 22 7 → 135 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_38_22_7

#print axioms CoveringDesigns.lower_bound_38_22_7

#check (@CoveringDesigns.lower_bound_39_23_8 : ∀ {α : Type*} [Fintype α] {C : CoveringDesigns.Family α},
    Fintype.card α = 39 → CoveringDesigns.IsCover C 23 8 → 229 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_39_23_8

#print axioms CoveringDesigns.lower_bound_39_23_8

namespace CoveringDesigns.AuditSevenC1993All
universe u_1 u_2
#check (@CoveringDesigns.SevenBlock.classification_ge_two : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {a : ℕ},
  2 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 →
        CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 →
          Fintype.card I = 7 →
            ∃ (tag : Bool),
              CoveringDesigns.SevenBlock.IndexedIsomorphic B (CoveringDesigns.SevenBlock.templateBlock a tag))

#guard_standard_axioms CoveringDesigns.SevenBlock.classification_ge_two

#print axioms CoveringDesigns.SevenBlock.classification_ge_two

#check (@CoveringDesigns.SevenBlock.classification : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] [DecidableEq I] {a : ℕ},
  1 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 →
        CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 →
          Fintype.card I = 7 →
            ∃! tag : Bool,
              CoveringDesigns.SevenBlock.IndexedIsomorphic B (CoveringDesigns.SevenBlock.templateBlock a tag))

#guard_standard_axioms CoveringDesigns.SevenBlock.classification

#print axioms CoveringDesigns.SevenBlock.classification

#check (@CoveringDesigns.covering_number_19_9_3 : (∃ (C : CoveringDesigns.Family (Fin 19)),
    CoveringDesigns.IsCover C 9 3 ∧ Finset.card C = 17) ∧
  ∀ (C : CoveringDesigns.Family (Fin 19)), CoveringDesigns.IsCover C 9 3 → 17 ≤ Finset.card C)

#guard_standard_axioms CoveringDesigns.covering_number_19_9_3

#print axioms CoveringDesigns.covering_number_19_9_3

#check (@CoveringDesigns.SevenBlock.classification_ge_two_expanded : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {a : ℕ},
  2 ≤ a →
    ∀ (B : I → Finset V),
      Fintype.card V = 7 * a + 4 →
        Fintype.card I = 7 →
          (∀ (i : I), (B i).card = 3 * a + 2) →
            (∀ (T : Finset V), T.card = 2 → ∃ (i : I), T ⊆ B i) →
              ∃ (tag : Bool) (e : V ≃ CoveringDesigns.SevenBlock.TemplatePoint a tag) (f : I ≃ Fin 7),
                ∀ (x : V) (i : I), x ∈ B i ↔ e x ∈ CoveringDesigns.SevenBlock.templateBlock a tag (f i))

#guard_standard_axioms CoveringDesigns.SevenBlock.classification_ge_two_expanded

#print axioms CoveringDesigns.SevenBlock.classification_ge_two_expanded

#check (@CoveringDesigns.SevenBlock.classification_expanded : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [DecidableEq V]
  [inst_2 : Fintype I] [DecidableEq I] {a : ℕ},
  1 ≤ a →
    ∀ (B : I → Finset V),
      Fintype.card V = 7 * a + 4 →
        Fintype.card I = 7 →
          (∀ (i : I), (B i).card = 3 * a + 2) →
            (∀ (T : Finset V), T.card = 2 → ∃ (i : I), T ⊆ B i) →
              ∃! tag : Bool,
                ∃ (e : V ≃ CoveringDesigns.SevenBlock.TemplatePoint a tag) (f : I ≃ Fin 7),
                  ∀ (x : V) (i : I), x ∈ B i ↔ e x ∈ CoveringDesigns.SevenBlock.templateBlock a tag (f i))

#guard_standard_axioms CoveringDesigns.SevenBlock.classification_expanded

#print axioms CoveringDesigns.SevenBlock.classification_expanded

#check (@CoveringDesigns.covering_number_19_9_3_expanded_on : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V],
  Fintype.card V = 19 →
    (∃ (C : Finset (Finset V)), C.card = 17 ∧ (∀ B ∈ C, B.card = 9) ∧ ∀ (T : Finset V), T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧
      ∀ (C : Finset (Finset V)), (∀ B ∈ C, B.card = 9) → (∀ (T : Finset V), T.card = 3 → ∃ B ∈ C, T ⊆ B) → 17 ≤ C.card)

#guard_standard_axioms CoveringDesigns.covering_number_19_9_3_expanded_on

#print axioms CoveringDesigns.covering_number_19_9_3_expanded_on

#check (@CoveringDesigns.C19_9_3.seventeen_le_card_expanded : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [DecidableEq V]
  [inst_2 : Fintype I] (B : I → Finset V),
  Fintype.card V = 19 →
    (∀ (i : I), (B i).card = 9) → (∀ (T : Finset V), T.card = 3 → ∃ (i : I), T ⊆ B i) → 17 ≤ Fintype.card I)

#guard_standard_axioms CoveringDesigns.C19_9_3.seventeen_le_card_expanded

#print axioms CoveringDesigns.C19_9_3.seventeen_le_card_expanded

#check (@CoveringDesigns.SevenBlock.covering_number_on : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {a : ℕ},
  1 ≤ a →
    Fintype.card V = 7 * a + 4 →
      (∃ (C : CoveringDesigns.Family V), CoveringDesigns.IsCover C (3 * a + 2) 2 ∧ Finset.card C = 7) ∧
        ∀ (C : CoveringDesigns.Family V), CoveringDesigns.IsCover C (3 * a + 2) 2 → 7 ≤ Finset.card C)

#guard_standard_axioms CoveringDesigns.SevenBlock.covering_number_on

#print axioms CoveringDesigns.SevenBlock.covering_number_on

#check (@CoveringDesigns.SevenBlock.templates_not_isomorphic : ∀ (a : ℕ),
  ¬CoveringDesigns.SevenBlock.IndexedIsomorphic (CoveringDesigns.SevenBlock.templateBlock a Bool.false)
      (CoveringDesigns.SevenBlock.templateBlock a Bool.true))

#guard_standard_axioms CoveringDesigns.SevenBlock.templates_not_isomorphic

#print axioms CoveringDesigns.SevenBlock.templates_not_isomorphic

#check (@CoveringDesigns.knownCover17_19_9_3_on_isCover : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (hv : Fintype.card α = 19), CoveringDesigns.IsCover (CoveringDesigns.knownCover17_19_9_3_on hv) 9 3)

#guard_standard_axioms CoveringDesigns.knownCover17_19_9_3_on_isCover

#print axioms CoveringDesigns.knownCover17_19_9_3_on_isCover

#check (@CoveringDesigns.knownBlocks17_19_9_3_distinct : CoveringDesigns.knownBlocks17_19_9_3.Nodup)

#guard_standard_axioms CoveringDesigns.knownBlocks17_19_9_3_distinct

#print axioms CoveringDesigns.knownBlocks17_19_9_3_distinct

#check (@CoveringDesigns.triple_count_19_9_3 : (Finset.powersetCard 3 Finset.univ).card = 969)

#guard_standard_axioms CoveringDesigns.triple_count_19_9_3

#print axioms CoveringDesigns.triple_count_19_9_3

end CoveringDesigns.AuditSevenC1993All

namespace CoveringDesigns.AuditProjectiveLinkAll
universe u v
#check (@ProjectiveLinkBounds.indexed_lower_bound :
  ∀ {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]
    {q : ℕ}, 3 ≤ q → Odd q → ∀ {B : ι → Finset α},
    Fintype.card α = q^2+q+2 → Multicover.IsCover B (q+2) 3 1 →
    ProjectiveLinkBounds.familyBound q ≤ Fintype.card ι)

#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound

#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound

#check (@ProjectiveLinkBounds.indexed_weak_lower_bound :
  ∀ {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]
    {q : ℕ}, 5 ≤ q → Odd q → ∀ {B : ι → Finset α},
    Fintype.card α = q^2+q+2 → Multicover.IsCover B (q+2) 3 1 →
    ProjectiveLinkBounds.weakBound q ≤ Fintype.card ι)

#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_lower_bound

#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_lower_bound

end CoveringDesigns.AuditProjectiveLinkAll

namespace CoveringDesigns.AuditProjectiveLinkDirectAll
#check (@ProjectiveLinkBounds.indexed_completion_lower_bound :
  ∀ {α : Type*} {ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    {q : ℕ}, 3 ≤ q → Odd q → ∀ {B : ι → Finset α},
    Fintype.card α = q^2+q+2 → Multicover.IsCover B (q+2) 3 1 →
    ProjectiveLinkBounds.pointCount q + Schoenheim.ceilDiv
      (ProjectiveLinkBounds.tripleDemand q) (ProjectiveLinkBounds.capacity q) ≤ Fintype.card ι)

#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_completion_lower_bound

#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_completion_lower_bound

end CoveringDesigns.AuditProjectiveLinkDirectAll

#check (@CoveringDesigns.TruncatedPlaneLoads.real_classification_iff :
  ∀ {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
    {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G), 4 ≤ q →
    ∀ {H : Finset (Finset V)} {w : Finset V → ℝ} {K : ℝ}, 0 < K →
      (CoveringDesigns.TruncatedPlaneLoads.Admissible P H w K ↔
        CoveringDesigns.TruncatedPlaneLoads.Description P H w (K/q)))

#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.real_classification_iff

#print axioms CoveringDesigns.TruncatedPlaneLoads.real_classification_iff

#check (@CoveringDesigns.PairEquality.geometric_dichotomy :
  ∀ {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}, 4 ≤ q →
    ∀ {H : Finset (Finset I)} {w : Finset I → ℝ},
      CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
      (∃ P : CoveringDesigns.TruncatedPlaneLoads.Plane q I (Fin (q+1)), P.core ⊆ H) ∨
        CoveringDesigns.PairEquality.IsTwistedPlane q H)

#guard_standard_axioms CoveringDesigns.PairEquality.geometric_dichotomy

#print axioms CoveringDesigns.PairEquality.geometric_dichotomy

namespace CoveringDesigns.AuditC4kAll
universe u_1 u_2
#check (@CoveringDesigns.PairDivisibility.divisibility :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [DecidableEq I] [inst_2 : Fintype X] [inst_3 : DecidableEq X]
  {q k : ℕ} {B : I → Finset X},
  4 ≤ q →
    q ≤ k →
      Fintype.card X = q * k →
        Fintype.card I = q * (q + 1) → CoveringDesigns.Multicover.IsCover B k 2 1 → q ∣ k ∨ q + 1 ∣ k)

#guard_standard_axioms CoveringDesigns.PairDivisibility.divisibility

#print axioms CoveringDesigns.PairDivisibility.divisibility

#check (@CoveringDesigns.TwistedArithmetic.no_twisted_four :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {H : Finset (Finset I)},
  CoveringDesigns.PairEquality.IsTwistedPlane 4 H → False)

#guard_standard_axioms CoveringDesigns.TwistedArithmetic.no_twisted_four

#print axioms CoveringDesigns.TwistedArithmetic.no_twisted_four

#check (@CoveringDesigns.PairConstructions.weighted_projective :
∀ {α : Type u_1} [inst : Fintype α] {q u r : ℕ},
  IsPrimePow q →
    2 ≤ q →
      1 ≤ r →
        r ≤ u →
          Fintype.card α = q * (q * u + r) →
            ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C (q * u + r) 2 ∧ Finset.card C ≤ q * q + q + 1)

#guard_standard_axioms CoveringDesigns.PairConstructions.weighted_projective

#print axioms CoveringDesigns.PairConstructions.weighted_projective

#check (@CoveringDesigns.C4k_K_2.exactness :
∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  8 ≤ k →
    Fintype.card α = 4 * k →
      (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 2 ∧ Finset.card C = if 4 ∣ k then 20 else 21) ∧
        ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C k 2 → (if 4 ∣ k then 20 else 21) ≤ Finset.card C)

#guard_standard_axioms CoveringDesigns.C4k_K_2.exactness

#print axioms CoveringDesigns.C4k_K_2.exactness

end CoveringDesigns.AuditC4kAll

#check (@CoveringDesigns.Qk_K_2.exact_90_10_2 :
  ∀ {α : Type*} [Fintype α], Fintype.card α = 90 →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 10 2 ∧ C.card = 91) ∧
      ∀ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 10 2 → 91 ≤ C.card)

#guard_standard_axioms CoveringDesigns.Qk_K_2.exact_90_10_2

#print axioms CoveringDesigns.Qk_K_2.exact_90_10_2

#check (@CoveringDesigns.PairConsequences.lower_bound_99_23_6 :
  ∀ {X : Type*} [Fintype X] {C : CoveringDesigns.Family X}, Fintype.card X = 99 →
    CoveringDesigns.IsCover C 23 6 → 13215 ≤ C.card)

#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_99_23_6

#print axioms CoveringDesigns.PairConsequences.lower_bound_99_23_6

#check (@CoveringDesigns.C6k_K_2.lower_bound :
  ∀ {X : Type*} [Fintype X] {C : CoveringDesigns.Family X} {k : ℕ},
    6 ≤ k → Fintype.card X = 6*k → CoveringDesigns.IsCover C k 2 → 43 ≤ C.card)

#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound

#print axioms CoveringDesigns.C6k_K_2.lower_bound

