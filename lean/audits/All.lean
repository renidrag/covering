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

