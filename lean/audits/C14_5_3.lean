import CoveringDesigns.C14_5_3.Examples

set_option linter.unusedVariables false

open CoveringDesigns Finset
open scoped BigOperators
universe u v w u_1 u_2 u_3 u_4

#print CoveringDesigns.IsCover
#print CoveringDesigns.Multicover.IsCover
#print CoveringDesigns.ExactDesign.IsDesign
#print CoveringDesigns.C14_5_3.IsCompletion
#print CoveringDesigns.C14_5_3.Irredundant
#print CoveringDesigns.C14_5_3.SpecialAt
#print CoveringDesigns.C14_5_3.chargedTriples
#print CoveringDesigns.C14_5_3.completedBlocks

namespace CoveringDesigns.Audit14_5_3

/-- Expanded ordinary interval: only uniformity and triple coverage are assumed. -/
theorem covering_interval_explicit {α : Type*} [Fintype α]
    (hv : Fintype.card α = 14) :
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 5) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 41 ≤ C.card) ∧
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 5) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 43) := by
  obtain ⟨hl,⟨C,hC,hcard⟩⟩ := covering_interval_14_5_3_on hv
  exact ⟨fun C hu hc => hl C ⟨hu,hc⟩,C,hC.1,hC.2,hcard⟩

theorem indexed_explicit {α ι : Type*} [Fintype α] [Fintype ι]
    (B : ι → Finset α) (hv : Fintype.card α = 14)
    (hu : ∀ i, (B i).card = 5)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) :
    41 ≤ Fintype.card ι := indexed_lower_bound_14_5_3 B hv hu hc

/-- Design and completion conditions expanded, with occurrence indices retained. -/
theorem completion_explicit {α ι κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [Fintype κ] (L : ι → Finset α) (B : κ → Finset α)
    (hv : Fintype.card α = 13) (hl : ∀ i, (L i).card = 4)
    (hp : ∀ P : Finset α, P.card = 2 → ∃! i, P ⊆ L i)
    (hb : ∀ i, (B i).card = 5)
    (hc : ∀ T : Finset α, T.card = 3 → (∀ i, ¬ T ⊆ L i) → ∃ j, T ⊆ B j) :
    28 ≤ Fintype.card κ := by
  classical
  apply C14_5_3.completion_at_least_28 hv
    ⟨hl,fun P hP => (C14_5_3.multiplicity_one_iff L P).mpr (hp P hP)⟩
  refine ⟨hb,?_⟩
  intro T hT
  have ht := Finset.mem_filter.mp hT
  have hh : ∀ i, ¬ T ⊆ L i := by
    intro i hi
    have := (C14_5_3.multiplicity_pos_iff L T).mpr ⟨i,hi⟩
    omega
  have he := hc T (Finset.mem_powersetCard.mp ht.1).2 hh
  have := (C14_5_3.multiplicity_pos_iff B T).mpr he
  omega

end CoveringDesigns.Audit14_5_3

-- Full fixed contracts, followed by transitive foundational-axiom guards.

#check (@CoveringDesigns.C14_5_3.linkPairExcess_self : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (x : α), CoveringDesigns.C14_5_3.linkPairExcess B x x = 0)
#guard_standard_axioms CoveringDesigns.C14_5_3.linkPairExcess_self
#print axioms CoveringDesigns.C14_5_3.linkPairExcess_self

#check (@CoveringDesigns.C14_5_3.linkPairExcess_comm : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (x y : α),
  CoveringDesigns.C14_5_3.linkPairExcess B x y = CoveringDesigns.C14_5_3.linkPairExcess B y x)
#guard_standard_axioms CoveringDesigns.C14_5_3.linkPairExcess_comm
#print axioms CoveringDesigns.C14_5_3.linkPairExcess_comm

#check (@CoveringDesigns.C14_5_3.pair_link_point_floor : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 → CoveringDesigns.Multicover.IsCover B 4 2 1 → ∀ (x : α), 4 ≤ CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.C14_5_3.pair_link_point_floor
#print axioms CoveringDesigns.C14_5_3.pair_link_point_floor

#check (@CoveringDesigns.C14_5_3.link_excess_sum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 → ∑ x, CoveringDesigns.C14_5_3.linkPointExcess B x = 4)
#guard_standard_axioms CoveringDesigns.C14_5_3.link_excess_sum
#print axioms CoveringDesigns.C14_5_3.link_excess_sum

#check (@CoveringDesigns.C14_5_3.link_excess_row : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      ∀ (x : α), ∑ y, CoveringDesigns.C14_5_3.linkPairExcess B x y = 3 * CoveringDesigns.C14_5_3.linkPointExcess B x)
#guard_standard_axioms CoveringDesigns.C14_5_3.link_excess_row
#print axioms CoveringDesigns.C14_5_3.link_excess_row

#check (@CoveringDesigns.C14_5_3.link_pair_excess_zero : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      ∀ {x : α},
        x ∉ CoveringDesigns.C14_5_3.linkHighPoints B → ∀ (y : α), CoveringDesigns.C14_5_3.linkPairExcess B x y = 0)
#guard_standard_axioms CoveringDesigns.C14_5_3.link_pair_excess_zero
#print axioms CoveringDesigns.C14_5_3.link_pair_excess_zero

#check (@CoveringDesigns.C14_5_3.high_excess_sum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∑ x ∈ CoveringDesigns.C14_5_3.linkHighPoints B, CoveringDesigns.C14_5_3.linkPointExcess B x = 4)
#guard_standard_axioms CoveringDesigns.C14_5_3.high_excess_sum
#print axioms CoveringDesigns.C14_5_3.high_excess_sum

#check (@CoveringDesigns.C14_5_3.high_excess_row : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      ∀ (x : α),
        ∑ y ∈ CoveringDesigns.C14_5_3.linkHighPoints B, CoveringDesigns.C14_5_3.linkPairExcess B x y =
          3 * CoveringDesigns.C14_5_3.linkPointExcess B x)
#guard_standard_axioms CoveringDesigns.C14_5_3.high_excess_row
#print axioms CoveringDesigns.C14_5_3.high_excess_row

#check (@CoveringDesigns.C14_5_3.high_excess_pos : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α} {x : α},
  x ∈ CoveringDesigns.C14_5_3.linkHighPoints B → 1 ≤ CoveringDesigns.C14_5_3.linkPointExcess B x)
#guard_standard_axioms CoveringDesigns.C14_5_3.high_excess_pos
#print axioms CoveringDesigns.C14_5_3.high_excess_pos

#check (@CoveringDesigns.C14_5_3.pair_support_union : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (a b c : α),
  CoveringDesigns.indexedSubsetDegree B {a, b} + CoveringDesigns.indexedSubsetDegree B {a, c} ≤
    CoveringDesigns.indexedDegree B a + CoveringDesigns.indexedSubsetDegree B {b, c})
#guard_standard_axioms CoveringDesigns.C14_5_3.pair_support_union
#print axioms CoveringDesigns.C14_5_3.pair_support_union

#check (@CoveringDesigns.C14_5_3.high_points_card : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 → (CoveringDesigns.C14_5_3.linkHighPoints B).card = 4)
#guard_standard_axioms CoveringDesigns.C14_5_3.high_points_card
#print axioms CoveringDesigns.C14_5_3.high_points_card

#check (@CoveringDesigns.C14_5_3.high_degree_five : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∀ {x : α}, x ∈ CoveringDesigns.C14_5_3.linkHighPoints B → CoveringDesigns.indexedDegree B x = 5)
#guard_standard_axioms CoveringDesigns.C14_5_3.high_degree_five
#print axioms CoveringDesigns.C14_5_3.high_degree_five

#check (@CoveringDesigns.C14_5_3.low_degree_four : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      ∀ {x : α}, x ∉ CoveringDesigns.C14_5_3.linkHighPoints B → CoveringDesigns.indexedDegree B x = 4)
#guard_standard_axioms CoveringDesigns.C14_5_3.low_degree_four
#print axioms CoveringDesigns.C14_5_3.low_degree_four

#check (@CoveringDesigns.C14_5_3.low_pair_exact : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      ∀ {x y : α},
        x ≠ y → x ∉ CoveringDesigns.C14_5_3.linkHighPoints B → CoveringDesigns.indexedSubsetDegree B {x, y} = 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.low_pair_exact
#print axioms CoveringDesigns.C14_5_3.low_pair_exact

#check (@CoveringDesigns.C14_5_3.almost_small_intersections : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      ∀ {i : ι}, (B i ∩ CoveringDesigns.C14_5_3.linkHighPoints B).card ≤ 1 → ∀ {j : ι}, j ≠ i → (B j ∩ B i).card ≤ 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.almost_small_intersections
#print axioms CoveringDesigns.C14_5_3.almost_small_intersections

#check (@CoveringDesigns.C14_5_3.almost_intersection_sum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∀ (i : ι), ∑ j, (B j ∩ B i).card = 16 + (B i ∩ CoveringDesigns.C14_5_3.linkHighPoints B).card)
#guard_standard_axioms CoveringDesigns.C14_5_3.almost_intersection_sum
#print axioms CoveringDesigns.C14_5_3.almost_intersection_sum

#check (@CoveringDesigns.C14_5_3.small_intersection_balance : ∀ {ι : Type u_1} [inst : Fintype ι] (f : ι → ℕ) (i : ι),
  Fintype.card ι = 14 → f i = 4 → (∀ (j : ι), j ≠ i → f j ≤ 1) → {j ∈ (Finset.univ : Finset ι) | f j = 0}.card + ∑ j, f j = 17)
#guard_standard_axioms CoveringDesigns.C14_5_3.small_intersection_balance
#print axioms CoveringDesigns.C14_5_3.small_intersection_balance

#check (@CoveringDesigns.C14_5_3.one_high_meets_all : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∀ {i : ι}, (B i ∩ CoveringDesigns.C14_5_3.linkHighPoints B).card = 1 → ∀ {j : ι}, j ≠ i → (B j ∩ B i).card = 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.one_high_meets_all
#print axioms CoveringDesigns.C14_5_3.one_high_meets_all

#check (@CoveringDesigns.C14_5_3.low_block_unique_disjoint : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∀ {i : ι}, (B i ∩ CoveringDesigns.C14_5_3.linkHighPoints B).card = 0 → ∃! j, (B j ∩ B i).card = 0)
#guard_standard_axioms CoveringDesigns.C14_5_3.low_block_unique_disjoint
#print axioms CoveringDesigns.C14_5_3.low_block_unique_disjoint

#check (@CoveringDesigns.C14_5_3.one_high_pair_two : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∀ {i : ι} {a : α},
          B i ∩ CoveringDesigns.C14_5_3.linkHighPoints B = {a} →
            ∀ {y : α},
              y ∈ CoveringDesigns.C14_5_3.linkHighPoints B → y ≠ a → CoveringDesigns.indexedSubsetDegree B {y, a} = 2)
#guard_standard_axioms CoveringDesigns.C14_5_3.one_high_pair_two
#print axioms CoveringDesigns.C14_5_3.one_high_pair_two

#check (@CoveringDesigns.C14_5_3.four_point_regular : ∀ {α : Type u_1} [Fintype α] [DecidableEq α] (H : Finset α),
  H.card = 4 →
    ∀ (f : α → α → ℕ),
      (∀ (x y : α), f x y = f y x) →
        (∀ (x : α), f x x = 0) →
          (∀ x ∈ H, ∑ y ∈ H, f x y = 3) →
            ∀ {a : α}, a ∈ H → (∀ y ∈ H, y ≠ a → f a y = 1) → ∀ {x y : α}, x ∈ H → y ∈ H → x ≠ y → f x y = 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.four_point_regular
#print axioms CoveringDesigns.C14_5_3.four_point_regular

#check (@CoveringDesigns.C14_5_3.high_pair_excess_one : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∀ {x y : α},
          x ∈ CoveringDesigns.C14_5_3.linkHighPoints B →
            y ∈ CoveringDesigns.C14_5_3.linkHighPoints B → x ≠ y → CoveringDesigns.C14_5_3.linkPairExcess B x y = 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.high_pair_excess_one
#print axioms CoveringDesigns.C14_5_3.high_pair_excess_one

#check (@CoveringDesigns.C14_5_3.almost_pair_profile : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∀ {P : Finset α},
          P.card = 2 →
            CoveringDesigns.indexedSubsetDegree B P = if P ⊆ CoveringDesigns.C14_5_3.linkHighPoints B then 2 else 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.almost_pair_profile
#print axioms CoveringDesigns.C14_5_3.almost_pair_profile

#check (@CoveringDesigns.C14_5_3.almost_high_block : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 → ∃ j, B j = CoveringDesigns.C14_5_3.linkHighPoints B)
#guard_standard_axioms CoveringDesigns.C14_5_3.almost_high_block
#print axioms CoveringDesigns.C14_5_3.almost_high_block

#check (@CoveringDesigns.C14_5_3.delete_index_balance : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (B : ι → Finset α) (i : ι) (T : Finset α),
  (CoveringDesigns.indexedSubsetDegree (fun j : {j : ι // j ≠ i} => B j.val) T + if T ⊆ B i then 1 else 0) =
    CoveringDesigns.indexedSubsetDegree B T)
#guard_standard_axioms CoveringDesigns.C14_5_3.delete_index_balance
#print axioms CoveringDesigns.C14_5_3.delete_index_balance

#check (@CoveringDesigns.C14_5_3.almost_exact_deletion : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∃ i, B i = CoveringDesigns.C14_5_3.linkHighPoints B ∧ CoveringDesigns.ExactDesign.IsDesign (fun j : {j : ι // j ≠ i} => B j.val) 4 2 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.almost_exact_deletion
#print axioms CoveringDesigns.C14_5_3.almost_exact_deletion

#check (@CoveringDesigns.C14_5_3.subset_filter_powerset : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (S : Finset α) (r : ℕ), {x ∈ Finset.powersetCard r Finset.univ | x ⊆ S} = Finset.powersetCard r S)
#guard_standard_axioms CoveringDesigns.C14_5_3.subset_filter_powerset
#print axioms CoveringDesigns.C14_5_3.subset_filter_powerset

#check (@CoveringDesigns.C14_5_3.low_pair_exact_of_not_subset : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      ∀ {P : Finset α},
        P.card = 2 → ¬P ⊆ CoveringDesigns.C14_5_3.linkHighPoints B → CoveringDesigns.indexedSubsetDegree B P = 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.low_pair_exact_of_not_subset
#print axioms CoveringDesigns.C14_5_3.low_pair_exact_of_not_subset

#check (@CoveringDesigns.C14_5_3.high_pair_sum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        ∑ P ∈ Finset.powersetCard 2 (CoveringDesigns.C14_5_3.linkHighPoints B),
            CoveringDesigns.indexedSubsetDegree B P =
          12)
#guard_standard_axioms CoveringDesigns.C14_5_3.high_pair_sum
#print axioms CoveringDesigns.C14_5_3.high_pair_sum

#check (@CoveringDesigns.C14_5_3.bounded_fiber_sum : ∀ {ι : Type u_1} [inst : Fintype ι] (r : ι → ℕ) (n : ℕ),
  (∀ (i : ι), r i ≤ n) → ∀ (f : ℕ → ℕ), ∑ i, f (r i) = ∑ j ∈ Finset.range (n + 1), {i ∈ (Finset.univ : Finset ι) | r i = j}.card * f j)
#guard_standard_axioms CoveringDesigns.C14_5_3.bounded_fiber_sum
#print axioms CoveringDesigns.C14_5_3.bounded_fiber_sum

#check (@CoveringDesigns.C14_5_3.high_trace_moments : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        have n := CoveringDesigns.C14_5_3.traceCount B (CoveringDesigns.C14_5_3.linkHighPoints B);
        n 0 + n 1 + n 2 + n 3 + n 4 = 14 ∧ n 1 + 2 * n 2 + 3 * n 3 + 4 * n 4 = 20 ∧ n 2 + 3 * n 3 + 6 * n 4 = 12)
#guard_standard_axioms CoveringDesigns.C14_5_3.high_trace_moments
#print axioms CoveringDesigns.C14_5_3.high_trace_moments

#check (@CoveringDesigns.C14_5_3.exists_one_high_block : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 → ∃ i, (B i ∩ CoveringDesigns.C14_5_3.linkHighPoints B).card = 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.exists_one_high_block
#print axioms CoveringDesigns.C14_5_3.exists_one_high_block

#check (@CoveringDesigns.C14_5_3.exists_low_block_of_no_high_block : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.Multicover.IsCover B 4 2 1 →
      Fintype.card ι = 14 →
        (∀ (i : ι), B i ≠ CoveringDesigns.C14_5_3.linkHighPoints B) →
          ∃ i, (B i ∩ CoveringDesigns.C14_5_3.linkHighPoints B).card = 0)
#guard_standard_axioms CoveringDesigns.C14_5_3.exists_low_block_of_no_high_block
#print axioms CoveringDesigns.C14_5_3.exists_low_block_of_no_high_block

#check (@CoveringDesigns.C14_5_3.collinearCount_pos : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
      ∀ {A : Finset α}, A.card = 5 → 1 ≤ CoveringDesigns.C14_5_3.collinearCount L A)
#guard_standard_axioms CoveringDesigns.C14_5_3.collinearCount_pos
#print axioms CoveringDesigns.C14_5_3.collinearCount_pos

#check (@CoveringDesigns.C14_5_3.collinear_sum : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] (L : ι → Finset α) (B : κ → Finset α),
  ∑ T ∈ CoveringDesigns.C14_5_3.collinearTriples L, CoveringDesigns.indexedSubsetDegree B T =
    ∑ i, CoveringDesigns.C14_5_3.collinearCount L (B i))
#guard_standard_axioms CoveringDesigns.C14_5_3.collinear_sum
#print axioms CoveringDesigns.C14_5_3.collinear_sum

#check (@CoveringDesigns.C14_5_3.triple_sum_split : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] (L : ι → Finset α) (B : κ → Finset α),
  ∑ T ∈ CoveringDesigns.C14_5_3.collinearTriples L, CoveringDesigns.indexedSubsetDegree B T +
      ∑ T ∈ CoveringDesigns.C14_5_3.noncollinearTriples L, CoveringDesigns.indexedSubsetDegree B T =
    ∑ T ∈ Finset.powersetCard 3 Finset.univ, CoveringDesigns.indexedSubsetDegree B T)
#guard_standard_axioms CoveringDesigns.C14_5_3.triple_sum_split
#print axioms CoveringDesigns.C14_5_3.triple_sum_split

#check (@CoveringDesigns.C14_5_3.completion_slack : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α} {B : κ → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
      CoveringDesigns.C14_5_3.IsCompletion L B →
        CoveringDesigns.C14_5_3.completionLoss L B + CoveringDesigns.C14_5_3.completionExcess L B + 234 =
          9 * Fintype.card κ)
#guard_standard_axioms CoveringDesigns.C14_5_3.completion_slack
#print axioms CoveringDesigns.C14_5_3.completion_slack

#check (@CoveringDesigns.C14_5_3.completion_capacity : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α} {B : κ → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → CoveringDesigns.C14_5_3.IsCompletion L B → 26 ≤ Fintype.card κ)
#guard_standard_axioms CoveringDesigns.C14_5_3.completion_capacity
#print axioms CoveringDesigns.C14_5_3.completion_capacity

#check (@CoveringDesigns.C14_5_3.completion_equality : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α} {B : κ → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
      CoveringDesigns.C14_5_3.IsCompletion L B →
        Fintype.card κ = 26 →
          (∀ (i : κ), CoveringDesigns.C14_5_3.collinearCount L (B i) = 1) ∧
            ∀ T ∈ CoveringDesigns.C14_5_3.noncollinearTriples L, CoveringDesigns.indexedSubsetDegree B T = 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.completion_equality
#print axioms CoveringDesigns.C14_5_3.completion_equality

#check (@CoveringDesigns.C14_5_3.collinear_pair_count : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {L : ι → Finset α},
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
    ∀ {P : Finset α},
      P.card = 2 →
        {T ∈ CoveringDesigns.LabelledCliques.extensions P | 0 < CoveringDesigns.indexedSubsetDegree L T}.card = 2)
#guard_standard_axioms CoveringDesigns.C14_5_3.collinear_pair_count
#print axioms CoveringDesigns.C14_5_3.collinear_pair_count

#check (@CoveringDesigns.C14_5_3.noncollinear_pair_count : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
      ∀ {P : Finset α},
        P.card = 2 →
          {T ∈ CoveringDesigns.LabelledCliques.extensions P | CoveringDesigns.indexedSubsetDegree L T = 0}.card = 9)
#guard_standard_axioms CoveringDesigns.C14_5_3.noncollinear_pair_count
#print axioms CoveringDesigns.C14_5_3.noncollinear_pair_count

#check (@CoveringDesigns.C14_5_3.completion_pair_identity : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α} {B : κ → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
      CoveringDesigns.C14_5_3.IsCompletion L B →
        ∀ {P : Finset α},
          P.card = 2 →
            3 * CoveringDesigns.indexedSubsetDegree B P =
              9 +
                  ∑ T ∈ CoveringDesigns.LabelledCliques.extensions P with CoveringDesigns.indexedSubsetDegree L T = 0,
                    (CoveringDesigns.indexedSubsetDegree B T - 1) +
                ∑ T ∈ CoveringDesigns.LabelledCliques.extensions P with 0 < CoveringDesigns.indexedSubsetDegree L T,
                  CoveringDesigns.indexedSubsetDegree B T)
#guard_standard_axioms CoveringDesigns.C14_5_3.completion_pair_identity
#print axioms CoveringDesigns.C14_5_3.completion_pair_identity

#check (@CoveringDesigns.C14_5_3.extensions_inside_pair : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (P : Finset α) {c d : α},
  c ∉ P →
    d ∉ P →
      c ≠ d → {x ∈ CoveringDesigns.LabelledCliques.extensions P | x ⊆ insert c (insert d P)} = {insert c P, insert d P})
#guard_standard_axioms CoveringDesigns.C14_5_3.extensions_inside_pair
#print axioms CoveringDesigns.C14_5_3.extensions_inside_pair

#check (@CoveringDesigns.C14_5_3.collinear_extensions_eq : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {L : ι → Finset α},
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
    ∀ {P : Finset α},
      P.card = 2 →
        ∀ {i : ι},
          P ⊆ L i →
            {T ∈ CoveringDesigns.LabelledCliques.extensions P | 0 < CoveringDesigns.indexedSubsetDegree L T} =
              {x ∈ CoveringDesigns.LabelledCliques.extensions P | x ⊆ L i})
#guard_standard_axioms CoveringDesigns.C14_5_3.collinear_extensions_eq
#print axioms CoveringDesigns.C14_5_3.collinear_extensions_eq

#check (@CoveringDesigns.C14_5_3.line_pair_sum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {L : ι → Finset α},
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
    ∀ (w : Finset α → ℕ) {P : Finset α},
      P.card = 2 →
        ∀ {i : ι} {c d : α},
          c ∉ P →
            d ∉ P →
              c ≠ d →
                L i = insert c (insert d P) →
                  ∑ T ∈ CoveringDesigns.LabelledCliques.extensions P with 0 < CoveringDesigns.indexedSubsetDegree L T,
                      w T =
                    w (insert c P) + w (insert d P))
#guard_standard_axioms CoveringDesigns.C14_5_3.line_pair_sum
#print axioms CoveringDesigns.C14_5_3.line_pair_sum

#check (@CoveringDesigns.C14_5_3.linewise_divisibility : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {L : ι → Finset α},
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
    ∀ (w : Finset α → ℕ),
      (∀ (P : Finset α),
          P.card = 2 →
            3 ∣
              ∑ T ∈ CoveringDesigns.LabelledCliques.extensions P with 0 < CoveringDesigns.indexedSubsetDegree L T,
                w T) →
        ∀ {T : Finset α}, T ∈ CoveringDesigns.C14_5_3.collinearTriples L → 3 ∣ w T)
#guard_standard_axioms CoveringDesigns.C14_5_3.linewise_divisibility
#print axioms CoveringDesigns.C14_5_3.linewise_divisibility

#check (@CoveringDesigns.C14_5_3.completion_at_least_27 : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α} {B : κ → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → CoveringDesigns.C14_5_3.IsCompletion L B → 27 ≤ Fintype.card κ)
#guard_standard_axioms CoveringDesigns.C14_5_3.completion_at_least_27
#print axioms CoveringDesigns.C14_5_3.completion_at_least_27

#check (@CoveringDesigns.C14_5_3.completed_uniform : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α} {B : κ → Finset α},
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
    CoveringDesigns.C14_5_3.IsCompletion L B →
      CoveringDesigns.Multicover.Uniform (CoveringDesigns.C14_5_3.completedBlocks L B) 5)
#guard_standard_axioms CoveringDesigns.C14_5_3.completed_uniform
#print axioms CoveringDesigns.C14_5_3.completed_uniform

#check (@CoveringDesigns.C14_5_3.completed_covers_new : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [Fintype α]
  [inst : DecidableEq α] [inst_1 : Fintype ι] [Fintype κ] {L : ι → Finset α} (B : κ → Finset α),
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
    ∀ {P : Finset α},
      P.card = 2 →
        ∃ i, insert none (Finset.map Function.Embedding.some P) ⊆ CoveringDesigns.C14_5_3.completedBlocks L B i)
#guard_standard_axioms CoveringDesigns.C14_5_3.completed_covers_new
#print axioms CoveringDesigns.C14_5_3.completed_covers_new

#check (@CoveringDesigns.C14_5_3.completed_covers_collinear : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [Fintype α]
  [inst : DecidableEq α] [inst_1 : Fintype ι] [Fintype κ] {L : ι → Finset α} (B : κ → Finset α) {T : Finset α},
  0 < CoveringDesigns.indexedSubsetDegree L T →
    ∃ i, Finset.map Function.Embedding.some T ⊆ CoveringDesigns.C14_5_3.completedBlocks L B i)
#guard_standard_axioms CoveringDesigns.C14_5_3.completed_covers_collinear
#print axioms CoveringDesigns.C14_5_3.completed_covers_collinear

#check (@CoveringDesigns.C14_5_3.completed_covers_noncollinear : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3}
  [inst : Fintype α] [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α}
  {B : κ → Finset α},
  CoveringDesigns.C14_5_3.IsCompletion L B →
    ∀ {T : Finset α},
      T.card = 3 →
        CoveringDesigns.indexedSubsetDegree L T = 0 →
          ∃ i, Finset.map Function.Embedding.some T ⊆ CoveringDesigns.C14_5_3.completedBlocks L B i)
#guard_standard_axioms CoveringDesigns.C14_5_3.completed_covers_noncollinear
#print axioms CoveringDesigns.C14_5_3.completed_covers_noncollinear

#check (@CoveringDesigns.C14_5_3.completed_isCover : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α} {B : κ → Finset α},
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
    CoveringDesigns.C14_5_3.IsCompletion L B →
      CoveringDesigns.Multicover.IsCover (CoveringDesigns.C14_5_3.completedBlocks L B) 5 3 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.completed_isCover
#print axioms CoveringDesigns.C14_5_3.completed_isCover

#check (@CoveringDesigns.C14_5_3.completion_at_least_28 : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α} {B : κ → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → CoveringDesigns.C14_5_3.IsCompletion L B → 28 ≤ Fintype.card κ)
#guard_standard_axioms CoveringDesigns.C14_5_3.completion_at_least_28
#print axioms CoveringDesigns.C14_5_3.completion_at_least_28

#check (@CoveringDesigns.C14_5_3.block_charge_capacity : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
      ∀ {A M : Finset α},
        A.card = 5 →
          M ⊆ A →
            9 ≤
              CoveringDesigns.C14_5_3.collinearCount L A - 1 + (CoveringDesigns.C14_5_3.chargedTriples L A M).card +
                (5 - M.card).choose 3)
#guard_standard_axioms CoveringDesigns.C14_5_3.block_charge_capacity
#print axioms CoveringDesigns.C14_5_3.block_charge_capacity

#check (@CoveringDesigns.C14_5_3.block_charge_five : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
      ∀ {A M : Finset α},
        A.card = 5 →
          M ⊆ A →
            M.Nonempty →
              5 ≤ CoveringDesigns.C14_5_3.collinearCount L A - 1 + (CoveringDesigns.C14_5_3.chargedTriples L A M).card)
#guard_standard_axioms CoveringDesigns.C14_5_3.block_charge_five
#print axioms CoveringDesigns.C14_5_3.block_charge_five

#check (@CoveringDesigns.C14_5_3.block_charge_eight : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
      ∀ {A M : Finset α},
        A.card = 5 →
          M ⊆ A →
            M.card = 2 →
              8 ≤ CoveringDesigns.C14_5_3.collinearCount L A - 1 + (CoveringDesigns.C14_5_3.chargedTriples L A M).card)
#guard_standard_axioms CoveringDesigns.C14_5_3.block_charge_eight
#print axioms CoveringDesigns.C14_5_3.block_charge_eight

#check (@CoveringDesigns.C14_5_3.disjoint_charge_budget : ∀ {α : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : Fintype κ] {L : ι → Finset α} {B : κ → Finset α}
  [DecidableEq κ] (S : Finset κ) (M : κ → Finset α),
  ((S : Set κ).PairwiseDisjoint fun i => CoveringDesigns.C14_5_3.chargedTriples L (B i) (M i)) →
    (∀ i ∈ S, ∀ T ∈ CoveringDesigns.C14_5_3.chargedTriples L (B i) (M i), 2 ≤ CoveringDesigns.indexedSubsetDegree B T) →
      ∑ i ∈ S,
          (CoveringDesigns.C14_5_3.collinearCount L (B i) - 1 +
            (CoveringDesigns.C14_5_3.chargedTriples L (B i) (M i)).card) ≤
        CoveringDesigns.C14_5_3.completionLoss L B + CoveringDesigns.C14_5_3.completionExcess L B)
#guard_standard_axioms CoveringDesigns.C14_5_3.disjoint_charge_budget
#print axioms CoveringDesigns.C14_5_3.disjoint_charge_budget

#check (@CoveringDesigns.C14_5_3.exact_line_count : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 → CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → Fintype.card ι = 13)
#guard_standard_axioms CoveringDesigns.C14_5_3.exact_line_count
#print axioms CoveringDesigns.C14_5_3.exact_line_count

#check (@CoveringDesigns.C14_5_3.exact_point_count : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 → CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → ∀ (x : α), CoveringDesigns.indexedDegree L x = 4)
#guard_standard_axioms CoveringDesigns.C14_5_3.exact_point_count
#print axioms CoveringDesigns.C14_5_3.exact_point_count

#check (@CoveringDesigns.C14_5_3.exact_unique_line : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] {L : ι → Finset α},
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → ∀ {P : Finset α}, P.card = 2 → ∃! i, P ⊆ L i)
#guard_standard_axioms CoveringDesigns.C14_5_3.exact_unique_line
#print axioms CoveringDesigns.C14_5_3.exact_unique_line

#check (@CoveringDesigns.C14_5_3.exact_line_intersection : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] {L : ι → Finset α},
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → ∀ {i j : ι}, i ≠ j → (L i ∩ L j).card ≤ 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.exact_line_intersection
#print axioms CoveringDesigns.C14_5_3.exact_line_intersection

#check (@CoveringDesigns.C14_5_3.exact_multiplicity_le_one : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] {L : ι → Finset α},
  CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
    ∀ {T : Finset α}, 2 ≤ T.card → CoveringDesigns.indexedSubsetDegree L T ≤ 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.exact_multiplicity_le_one
#print axioms CoveringDesigns.C14_5_3.exact_multiplicity_le_one

#check (@CoveringDesigns.C14_5_3.exact_lines_injective : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] {L : ι → Finset α}, CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → Function.Injective L)
#guard_standard_axioms CoveringDesigns.C14_5_3.exact_lines_injective
#print axioms CoveringDesigns.C14_5_3.exact_lines_injective

#check (@CoveringDesigns.C14_5_3.exact_lines_meet : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 → CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → ∀ (i j : ι), (L i ∩ L j).Nonempty)
#guard_standard_axioms CoveringDesigns.C14_5_3.exact_lines_meet
#print axioms CoveringDesigns.C14_5_3.exact_lines_meet

#check (@CoveringDesigns.C14_5_3.collinear_card : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → (CoveringDesigns.C14_5_3.collinearTriples L).card = 52)
#guard_standard_axioms CoveringDesigns.C14_5_3.collinear_card
#print axioms CoveringDesigns.C14_5_3.collinear_card

#check (@CoveringDesigns.C14_5_3.noncollinear_card : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 → (CoveringDesigns.C14_5_3.noncollinearTriples L).card = 234)
#guard_standard_axioms CoveringDesigns.C14_5_3.noncollinear_card
#print axioms CoveringDesigns.C14_5_3.noncollinear_card

#check (@CoveringDesigns.C14_5_3.degree_through_point : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (p q : α),
  CoveringDesigns.indexedDegree (fun i : {i : ι // p ∈ B i} => B i.val) q = CoveringDesigns.indexedSubsetDegree B {p, q})
#guard_standard_axioms CoveringDesigns.C14_5_3.degree_through_point
#print axioms CoveringDesigns.C14_5_3.degree_through_point

#check (@CoveringDesigns.C14_5_3.no_five_arc : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {L : ι → Finset α},
  Fintype.card α = 13 →
    CoveringDesigns.ExactDesign.IsDesign L 4 2 1 →
      ∀ (A : Finset α), A.card = 5 → ∃ T ∈ Finset.powersetCard 3 A, 0 < CoveringDesigns.indexedSubsetDegree L T)
#guard_standard_axioms CoveringDesigns.C14_5_3.no_five_arc
#print axioms CoveringDesigns.C14_5_3.no_five_arc

#check (@CoveringDesigns.C14_5_3.Boundary.repeated_cover : CoveringDesigns.Multicover.IsCover
  CoveringDesigns.C14_5_3.Boundary.repeated 5 3 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.Boundary.repeated_cover
#print axioms CoveringDesigns.C14_5_3.Boundary.repeated_cover

#check (@CoveringDesigns.C14_5_3.Boundary.repeated_not_irredundant : ¬CoveringDesigns.C14_5_3.Irredundant
    CoveringDesigns.C14_5_3.Boundary.repeated 3)
#guard_standard_axioms CoveringDesigns.C14_5_3.Boundary.repeated_not_irredundant
#print axioms CoveringDesigns.C14_5_3.Boundary.repeated_not_irredundant

#check (@CoveringDesigns.C14_5_3.Boundary.delete_one_still_covers : CoveringDesigns.Multicover.IsCover
  (fun i : {i : Fin 2 // i ≠ 0} => CoveringDesigns.C14_5_3.Boundary.repeated i.val) 5 3 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.Boundary.delete_one_still_covers
#print axioms CoveringDesigns.C14_5_3.Boundary.delete_one_still_covers

#check (@CoveringDesigns.C14_5_3.Boundary.delete_all_copies_fails : ¬CoveringDesigns.Multicover.IsCover
    (fun i : {i : Fin 2 // CoveringDesigns.C14_5_3.Boundary.repeated i ≠ CoveringDesigns.C14_5_3.Boundary.repeated 0} => CoveringDesigns.C14_5_3.Boundary.repeated i.val) 5 3 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.Boundary.delete_all_copies_fails
#print axioms CoveringDesigns.C14_5_3.Boundary.delete_all_copies_fails

#check (@CoveringDesigns.C14_5_3.Boundary.deletion_counts_one_occurrence : Fintype.card { i : Fin 2 // i ≠ 0 } = 1 ∧
  Fintype.card { i // CoveringDesigns.C14_5_3.Boundary.repeated i ≠ CoveringDesigns.C14_5_3.Boundary.repeated 0 } = 0)
#guard_standard_axioms CoveringDesigns.C14_5_3.Boundary.deletion_counts_one_occurrence
#print axioms CoveringDesigns.C14_5_3.Boundary.deletion_counts_one_occurrence

#check (@CoveringDesigns.C14_5_3.Boundary.almost_exact_without_injectivity : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (B : ι → Finset α),
  Fintype.card α = 13 →
    Fintype.card ι = 14 →
      (∀ (i : ι), (B i).card = 4) →
        (∀ (P : Finset α), P.card = 2 → ∃ i, P ⊆ B i) →
          ∃ i,
            B i = CoveringDesigns.C14_5_3.linkHighPoints B ∧ CoveringDesigns.ExactDesign.IsDesign (fun j : {j : ι // j ≠ i} => B j.val) 4 2 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.Boundary.almost_exact_without_injectivity
#print axioms CoveringDesigns.C14_5_3.Boundary.almost_exact_without_injectivity

#check (@CoveringDesigns.C14_5_3.Boundary.forty_private_without_structural_premises : ∀ {α : Type u_1} {ι : Type u_2}
  [inst : Fintype α] [DecidableEq α] [inst_2 : Fintype ι] (B : ι → Finset α),
  Fintype.card α = 14 →
    Fintype.card ι = 40 →
      (∀ (i : ι), (B i).card = 5) →
        (∀ (T : Finset α), T.card = 3 → ∃ i, T ⊆ B i) →
          ∀ (i : ι), ∃ T, T.card = 3 ∧ T ⊆ B i ∧ ∀ (j : ι), T ⊆ B j → j = i)
#guard_standard_axioms CoveringDesigns.C14_5_3.Boundary.forty_private_without_structural_premises
#print axioms CoveringDesigns.C14_5_3.Boundary.forty_private_without_structural_premises

#check (@CoveringDesigns.C14_5_3.exact_of_capacity : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α} {k t : ℕ},
  CoveringDesigns.Multicover.IsCover B k t 1 →
    k.choose t * Fintype.card ι = (Fintype.card α).choose t → CoveringDesigns.ExactDesign.IsDesign B k t 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.exact_of_capacity
#print axioms CoveringDesigns.C14_5_3.exact_of_capacity

#check (@CoveringDesigns.C14_5_3.point_floor : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 → CoveringDesigns.Multicover.IsCover B 5 3 1 → ∀ (x : α), 13 ≤ CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.C14_5_3.point_floor
#print axioms CoveringDesigns.C14_5_3.point_floor

#check (@CoveringDesigns.C14_5_3.pair_floor : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {P : Finset α}, P.card = 2 → 4 ≤ CoveringDesigns.indexedSubsetDegree B P)
#guard_standard_axioms CoveringDesigns.C14_5_3.pair_floor
#print axioms CoveringDesigns.C14_5_3.pair_floor

#check (@CoveringDesigns.C14_5_3.minimum_link_exact : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {x : α},
        CoveringDesigns.indexedDegree B x = 13 →
          CoveringDesigns.ExactDesign.IsDesign (CoveringDesigns.Multicover.subsetLink B {x}) 4 2 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.minimum_link_exact
#print axioms CoveringDesigns.C14_5_3.minimum_link_exact

#check (@CoveringDesigns.C14_5_3.residual_card : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (x : α),
  Fintype.card { i // x ∉ B i } = Fintype.card ι - CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.C14_5_3.residual_card
#print axioms CoveringDesigns.C14_5_3.residual_card

#check (@CoveringDesigns.C14_5_3.residual_uniform : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [Fintype ι] {B : ι → Finset α},
  CoveringDesigns.Multicover.Uniform B 5 →
    ∀ (x : α), CoveringDesigns.Multicover.Uniform (CoveringDesigns.C14_5_3.residualBlocks B x) 5)
#guard_standard_axioms CoveringDesigns.C14_5_3.residual_uniform
#print axioms CoveringDesigns.C14_5_3.residual_uniform

#check (@CoveringDesigns.C14_5_3.residual_completion : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  CoveringDesigns.Multicover.IsCover B 5 3 1 →
    ∀ (x : α),
      CoveringDesigns.C14_5_3.IsCompletion (CoveringDesigns.Multicover.subsetLink B {x})
        (CoveringDesigns.C14_5_3.residualBlocks B x))
#guard_standard_axioms CoveringDesigns.C14_5_3.residual_completion
#print axioms CoveringDesigns.C14_5_3.residual_completion

#check (@CoveringDesigns.C14_5_3.lower_bound_40 : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 → CoveringDesigns.Multicover.IsCover B 5 3 1 → 40 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.C14_5_3.lower_bound_40
#print axioms CoveringDesigns.C14_5_3.lower_bound_40

#check (@CoveringDesigns.C14_5_3.forty_irredundant : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 → Fintype.card ι = 40 → CoveringDesigns.C14_5_3.Irredundant B 3)
#guard_standard_axioms CoveringDesigns.C14_5_3.forty_irredundant
#print axioms CoveringDesigns.C14_5_3.forty_irredundant

#check (@CoveringDesigns.C14_5_3.Irredundant.injective : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [DecidableEq α] [Fintype ι]
  {B : ι → Finset α} {t : ℕ}, CoveringDesigns.C14_5_3.Irredundant B t → Function.Injective B)
#guard_standard_axioms CoveringDesigns.C14_5_3.Irredundant.injective
#print axioms CoveringDesigns.C14_5_3.Irredundant.injective

#check (@CoveringDesigns.C14_5_3.Irredundant.private_multiplicity : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α]
  [inst : DecidableEq α] [inst_1 : Fintype ι] {B : ι → Finset α} {t : ℕ},
  CoveringDesigns.C14_5_3.Irredundant B t →
    ∀ (i : ι), ∃ T, T.card = t ∧ T ⊆ B i ∧ CoveringDesigns.indexedSubsetDegree B T = 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.Irredundant.private_multiplicity
#print axioms CoveringDesigns.C14_5_3.Irredundant.private_multiplicity

#check (@CoveringDesigns.C14_5_3.tight_extensions : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α} {k m : ℕ},
  CoveringDesigns.Multicover.Uniform B k →
    ∀ (S : Finset α),
      (∀ T ∈ CoveringDesigns.LabelledCliques.extensions S, m ≤ CoveringDesigns.indexedSubsetDegree B T) →
        (k - S.card) * CoveringDesigns.indexedSubsetDegree B S = (Fintype.card α - S.card) * m →
          ∀ T ∈ CoveringDesigns.LabelledCliques.extensions S, CoveringDesigns.indexedSubsetDegree B T = m)
#guard_standard_axioms CoveringDesigns.C14_5_3.tight_extensions
#print axioms CoveringDesigns.C14_5_3.tight_extensions

#check (@CoveringDesigns.C14_5_3.minimum_pair_exact : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {x : α},
        CoveringDesigns.indexedDegree B x = 13 →
          ∀ {P : Finset α}, P.card = 2 → x ∈ P → CoveringDesigns.indexedSubsetDegree B P = 4)
#guard_standard_axioms CoveringDesigns.C14_5_3.minimum_pair_exact
#print axioms CoveringDesigns.C14_5_3.minimum_pair_exact

#check (@CoveringDesigns.C14_5_3.minimum_triple_exact : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {x : α},
        CoveringDesigns.indexedDegree B x = 13 →
          ∀ {T : Finset α}, T.card = 3 → x ∈ T → CoveringDesigns.indexedSubsetDegree B T = 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.minimum_triple_exact
#print axioms CoveringDesigns.C14_5_3.minimum_triple_exact

#check (@CoveringDesigns.C14_5_3.selected_trace_count : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [Fintype ι] [DecidableEq ι] (B : ι → Finset α) (S : Finset ι) (R : Finset α) (t : ℕ),
  ∑ P ∈ Finset.powersetCard t R, {i ∈ S | P ⊆ B i}.card = ∑ i ∈ S, (B i ∩ R).card.choose t)
#guard_standard_axioms CoveringDesigns.C14_5_3.selected_trace_count
#print axioms CoveringDesigns.C14_5_3.selected_trace_count

#check (@CoveringDesigns.C14_5_3.trace_complement_card : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [Fintype ι] {B : ι → Finset α},
  CoveringDesigns.Multicover.Uniform B 5 →
    ∀ {Z : Finset α} {p : α},
      p ∉ Z → ∀ {i : ι}, p ∈ B i → (B i ∩ (Finset.univ \ insert p Z)).card + (B i ∩ Z).card + 1 = 5)
#guard_standard_axioms CoveringDesigns.C14_5_3.trace_complement_card
#print axioms CoveringDesigns.C14_5_3.trace_complement_card

#check (@CoveringDesigns.C14_5_3.four_minimum_forces_sixteen : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {Z : Finset α},
        (∀ x ∈ Z, CoveringDesigns.indexedDegree B x = 13) → Z.card = 4 → ∃ p ∉ Z, 16 ≤ CoveringDesigns.indexedDegree B p)
#guard_standard_axioms CoveringDesigns.C14_5_3.four_minimum_forces_sixteen
#print axioms CoveringDesigns.C14_5_3.four_minimum_forces_sixteen

#check (@CoveringDesigns.C14_5_3.multiplicity_mono : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype ι]
  (B : ι → Finset α) {S T : Finset α},
  S ⊆ T → CoveringDesigns.indexedSubsetDegree B T ≤ CoveringDesigns.indexedSubsetDegree B S)
#guard_standard_axioms CoveringDesigns.C14_5_3.multiplicity_mono
#print axioms CoveringDesigns.C14_5_3.multiplicity_mono

#check (@CoveringDesigns.C14_5_3.multiplicity_pos_iff : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (T : Finset α), 0 < CoveringDesigns.indexedSubsetDegree B T ↔ ∃ i, T ⊆ B i)
#guard_standard_axioms CoveringDesigns.C14_5_3.multiplicity_pos_iff
#print axioms CoveringDesigns.C14_5_3.multiplicity_pos_iff

#check (@CoveringDesigns.C14_5_3.multiplicity_one_iff : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (T : Finset α), CoveringDesigns.indexedSubsetDegree B T = 1 ↔ ∃! i, T ⊆ B i)
#guard_standard_axioms CoveringDesigns.C14_5_3.multiplicity_one_iff
#print axioms CoveringDesigns.C14_5_3.multiplicity_one_iff

#check (@CoveringDesigns.C14_5_3.multiplicity_ge_two : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) {T : Finset α} {i j : ι},
  i ≠ j → T ⊆ B i → T ⊆ B j → 2 ≤ CoveringDesigns.indexedSubsetDegree B T)
#guard_standard_axioms CoveringDesigns.C14_5_3.multiplicity_ge_two
#print axioms CoveringDesigns.C14_5_3.multiplicity_ge_two

#check (@CoveringDesigns.C14_5_3.trace_count : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype ι]
  (B : ι → Finset α) (S : Finset α) (r : ℕ),
  ∑ T ∈ Finset.powersetCard r S, CoveringDesigns.indexedSubsetDegree B T = ∑ i, (B i ∩ S).card.choose r)
#guard_standard_axioms CoveringDesigns.C14_5_3.trace_count
#print axioms CoveringDesigns.C14_5_3.trace_count

#check (@CoveringDesigns.C14_5_3.intersection_sum : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype ι]
  (B : ι → Finset α) (S : Finset α), ∑ i, (B i ∩ S).card = ∑ x ∈ S, CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.C14_5_3.intersection_sum
#print axioms CoveringDesigns.C14_5_3.intersection_sum

#check (@CoveringDesigns.C14_5_3.selected_subset_count : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (A : Finset (Finset α)),
  ∑ T ∈ A, CoveringDesigns.indexedSubsetDegree B T = ∑ i, {x ∈ A | x ⊆ B i}.card)
#guard_standard_axioms CoveringDesigns.C14_5_3.selected_subset_count
#print axioms CoveringDesigns.C14_5_3.selected_subset_count

#check (@CoveringDesigns.C14_5_3.restrict_multiplicity : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (p : ι → Prop) [inst_2 : DecidablePred p] [inst_3 : Fintype { i // p i }]
  (T : Finset α), CoveringDesigns.indexedSubsetDegree (fun i : {i : ι // p i} => B i.val) T = {i ∈ (Finset.univ : Finset ι) | p i ∧ T ⊆ B i}.card)
#guard_standard_axioms CoveringDesigns.C14_5_3.restrict_multiplicity
#print axioms CoveringDesigns.C14_5_3.restrict_multiplicity

#check (@CoveringDesigns.C14_5_3.restrict_add_complement : ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (p : ι → Prop) [DecidablePred p] [inst_3 : Fintype { i // p i }]
  [inst_4 : Fintype { i // ¬p i }] (T : Finset α),
  CoveringDesigns.indexedSubsetDegree (fun i : {i : ι // p i} => B i.val) T + CoveringDesigns.indexedSubsetDegree (fun i : {i : ι // ¬ p i} => B i.val) T =
    CoveringDesigns.indexedSubsetDegree B T)
#guard_standard_axioms CoveringDesigns.C14_5_3.restrict_add_complement
#print axioms CoveringDesigns.C14_5_3.restrict_add_complement

#check (@CoveringDesigns.C14_5_3.forty_has_minimum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 → Fintype.card ι = 40 → ∃ x, CoveringDesigns.indexedDegree B x = 13)
#guard_standard_axioms CoveringDesigns.C14_5_3.forty_has_minimum
#print axioms CoveringDesigns.C14_5_3.forty_has_minimum

#check (@CoveringDesigns.C14_5_3.degree_profile_bound : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      Fintype.card ι = 40 →
        210 ≤ 200 + 2 * (CoveringDesigns.C14_5_3.minimumPoints B).card + (CoveringDesigns.C14_5_3.middlePoints B).card)
#guard_standard_axioms CoveringDesigns.C14_5_3.degree_profile_bound
#print axioms CoveringDesigns.C14_5_3.degree_profile_bound

#check (@CoveringDesigns.C14_5_3.not_forty : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 → CoveringDesigns.Multicover.IsCover B 5 3 1 → Fintype.card ι = 40 → False)
#guard_standard_axioms CoveringDesigns.C14_5_3.not_forty
#print axioms CoveringDesigns.C14_5_3.not_forty

#check (@CoveringDesigns.C14_5_3.indexed_lower_bound : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 → CoveringDesigns.Multicover.IsCover B 5 3 1 → 41 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.C14_5_3.indexed_lower_bound
#print axioms CoveringDesigns.C14_5_3.indexed_lower_bound

#check (@CoveringDesigns.C14_5_3.lower_bound : ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 14 → CoveringDesigns.IsCover C 5 3 → 41 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C14_5_3.lower_bound
#print axioms CoveringDesigns.C14_5_3.lower_bound

#check (@CoveringDesigns.C14_5_3.minimum_pair_trace_sum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {Z P : Finset α},
        (∀ x ∈ Z, CoveringDesigns.indexedDegree B x = 13) →
          P.card = 2 → Disjoint P Z → (∑ i, if P ⊆ B i then (B i ∩ Z).card else 0) = Z.card)
#guard_standard_axioms CoveringDesigns.C14_5_3.minimum_pair_trace_sum
#print axioms CoveringDesigns.C14_5_3.minimum_pair_trace_sum

#check (@CoveringDesigns.C14_5_3.no_five_minimum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {Z : Finset α}, (∀ x ∈ Z, CoveringDesigns.indexedDegree B x = 13) → Z.card = 5 → False)
#guard_standard_axioms CoveringDesigns.C14_5_3.no_five_minimum
#print axioms CoveringDesigns.C14_5_3.no_five_minimum

#check (@CoveringDesigns.C14_5_3.minimum_points_le_four : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {Z : Finset α}, (∀ x ∈ Z, CoveringDesigns.indexedDegree B x = 13) → Z.card ≤ 4)
#guard_standard_axioms CoveringDesigns.C14_5_3.minimum_points_le_four
#print axioms CoveringDesigns.C14_5_3.minimum_points_le_four

#check (@CoveringDesigns.C14_5_3.four_minimum_frame : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {Z : Finset α},
        (∀ x ∈ Z, CoveringDesigns.indexedDegree B x = 13) →
          Z.card = 4 →
            ∃ i,
              ∃ p ∉ Z,
                B i = insert p Z ∧
                  (∀ (j : ι), j ≠ i → (B j ∩ Z).card ≤ 2) ∧
                    {j ∈ (Finset.univ : Finset ι) | (B j ∩ Z).card = 1}.card = 12 ∧
                      (∀ (j : ι), (B j ∩ Z).card = 2 → p ∉ B j) ∧ ∀ (j : ι), (B j ∩ Z).card = 1 → p ∈ B j)
#guard_standard_axioms CoveringDesigns.C14_5_3.four_minimum_frame
#print axioms CoveringDesigns.C14_5_3.four_minimum_frame

#check (@CoveringDesigns.C14_5_3.missed_minimum_triple : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {x : α},
        CoveringDesigns.indexedDegree B x = 13 →
          ∀ (i : ι), x ∉ B i → ∃ T, T.card = 3 ∧ T ⊆ B i ∧ 2 ≤ CoveringDesigns.indexedSubsetDegree B T)
#guard_standard_axioms CoveringDesigns.C14_5_3.missed_minimum_triple
#print axioms CoveringDesigns.C14_5_3.missed_minimum_triple

#check (@CoveringDesigns.C14_5_3.minimum_trace_restriction : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {Z : Finset α}, (∀ x ∈ Z, CoveringDesigns.indexedDegree B x = 13) → ∀ (i : ι), ¬Z ⊆ B i → (B i ∩ Z).card ≤ 2)
#guard_standard_axioms CoveringDesigns.C14_5_3.minimum_trace_restriction
#print axioms CoveringDesigns.C14_5_3.minimum_trace_restriction

#check (@CoveringDesigns.C14_5_3.minimum_frame : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {Z : Finset α},
        (∀ x ∈ Z, CoveringDesigns.indexedDegree B x = 13) →
          3 ≤ Z.card → ∃ i, Z ⊆ B i ∧ ∀ (j : ι), j ≠ i → (B j ∩ Z).card ≤ 2)
#guard_standard_axioms CoveringDesigns.C14_5_3.minimum_frame
#print axioms CoveringDesigns.C14_5_3.minimum_frame

#check (@CoveringDesigns.C14_5_3.minimum_trace_moments : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {Z : Finset α},
        (∀ x ∈ Z, CoveringDesigns.indexedDegree B x = 13) →
          ∑ i, (B i ∩ Z).card = 13 * Z.card ∧ ∑ i, (B i ∩ Z).card.choose 2 = 4 * Z.card.choose 2)
#guard_standard_axioms CoveringDesigns.C14_5_3.minimum_trace_moments
#print axioms CoveringDesigns.C14_5_3.minimum_trace_moments

#check (@CoveringDesigns.C14_5_3.frame_trace_counts : ∀ {ι : Type u_1} [inst : Fintype ι] [DecidableEq ι] (f : ι → ℕ) (i : ι)
  (z : ℕ),
  f i = z →
    3 ≤ z →
      (∀ (j : ι), j ≠ i → f j ≤ 2) →
        ∑ j, f j = z + {j ∈ (Finset.univ : Finset ι) | f j = 1}.card + 2 * {j ∈ (Finset.univ : Finset ι) | f j = 2}.card ∧
          ∑ j, (f j).choose 2 = z.choose 2 + {j ∈ (Finset.univ : Finset ι) | f j = 2}.card)
#guard_standard_axioms CoveringDesigns.C14_5_3.frame_trace_counts
#print axioms CoveringDesigns.C14_5_3.frame_trace_counts

#check (@CoveringDesigns.C14_5_3.containing_trace_sum : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (P Z : Finset α),
  (∑ i, if P ⊆ B i then (B i ∩ Z).card else 0) = ∑ z ∈ Z, CoveringDesigns.indexedSubsetDegree B (insert z P))
#guard_standard_axioms CoveringDesigns.C14_5_3.containing_trace_sum
#print axioms CoveringDesigns.C14_5_3.containing_trace_sum

#check (@CoveringDesigns.C14_5_3.subtype_map_subset : ∀ {α : Type u_1} [Fintype α] [DecidableEq α] {p : α → Prop}
  [inst : DecidablePred p] (T : Finset { x // p x }) (A : Finset α),
  Finset.map (Function.Embedding.subtype p) T ⊆ A ↔ T ⊆ Finset.subtype p A)
#guard_standard_axioms CoveringDesigns.C14_5_3.subtype_map_subset
#print axioms CoveringDesigns.C14_5_3.subtype_map_subset

#check (@CoveringDesigns.C14_5_3.subtype_values_multiplicity : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α]
  [inst : DecidableEq α] [inst_1 : Fintype ι] {p : α → Prop} [inst_2 : DecidablePred p] (B : ι → Finset α)
  (T : Finset { x // p x }),
  CoveringDesigns.indexedSubsetDegree (fun i => Finset.subtype p (B i)) T =
    CoveringDesigns.indexedSubsetDegree B (Finset.map (Function.Embedding.subtype p) T))
#guard_standard_axioms CoveringDesigns.C14_5_3.subtype_values_multiplicity
#print axioms CoveringDesigns.C14_5_3.subtype_values_multiplicity

#check (@CoveringDesigns.C14_5_3.residual_multiplicity_split : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α]
  [inst : DecidableEq α] [inst_1 : Fintype ι] (B : ι → Finset α) (x : α) (T : Finset { p // p ∉ ({x} : Finset α) }),
  CoveringDesigns.indexedSubsetDegree (CoveringDesigns.Multicover.subsetLink B {x}) T +
      CoveringDesigns.indexedSubsetDegree (CoveringDesigns.C14_5_3.residualBlocks B x) T =
    CoveringDesigns.indexedSubsetDegree B (Finset.map (Function.Embedding.subtype fun p => p ∉ ({x} : Finset α)) T))
#guard_standard_axioms CoveringDesigns.C14_5_3.residual_multiplicity_split
#print axioms CoveringDesigns.C14_5_3.residual_multiplicity_split

#check (@CoveringDesigns.C14_5_3.residual_specials_card : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {x : α},
        CoveringDesigns.indexedDegree B x = 13 →
          (CoveringDesigns.C14_5_3.residualSpecials B x).card = (CoveringDesigns.C14_5_3.specialIndices B).card)
#guard_standard_axioms CoveringDesigns.C14_5_3.residual_specials_card
#print axioms CoveringDesigns.C14_5_3.residual_specials_card

#check (@CoveringDesigns.C14_5_3.residual_marks_nonempty : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α} {x : α} {i : { i // x ∉ B i }},
  i ∈ CoveringDesigns.C14_5_3.residualSpecials B x → (CoveringDesigns.C14_5_3.residualMarks B x i).Nonempty)
#guard_standard_axioms CoveringDesigns.C14_5_3.residual_marks_nonempty
#print axioms CoveringDesigns.C14_5_3.residual_marks_nonempty

#check (@CoveringDesigns.C14_5_3.residual_charges_disjoint : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      CoveringDesigns.C14_5_3.Irredundant B 3 →
        ∀ (x : α),
          ((CoveringDesigns.C14_5_3.residualSpecials B x) : Set {i : ι // x ∉ B i}).PairwiseDisjoint fun i =>
            CoveringDesigns.C14_5_3.chargedTriples (CoveringDesigns.Multicover.subsetLink B {x})
              (CoveringDesigns.C14_5_3.residualBlocks B x i) (CoveringDesigns.C14_5_3.residualMarks B x i))
#guard_standard_axioms CoveringDesigns.C14_5_3.residual_charges_disjoint
#print axioms CoveringDesigns.C14_5_3.residual_charges_disjoint

#check (@CoveringDesigns.C14_5_3.residual_charge_excess : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      CoveringDesigns.C14_5_3.Irredundant B 3 →
        ∀ (x : α) {i : { i // x ∉ B i }},
          i ∈ CoveringDesigns.C14_5_3.residualSpecials B x →
            ∀ {T : Finset { p // p ∉ ({x} : Finset α) }},
              T ∈
                  CoveringDesigns.C14_5_3.chargedTriples (CoveringDesigns.Multicover.subsetLink B {x})
                    (CoveringDesigns.C14_5_3.residualBlocks B x i) (CoveringDesigns.C14_5_3.residualMarks B x i) →
                CoveringDesigns.indexedSubsetDegree (CoveringDesigns.C14_5_3.residualBlocks B x) T = 2)
#guard_standard_axioms CoveringDesigns.C14_5_3.residual_charge_excess
#print axioms CoveringDesigns.C14_5_3.residual_charge_excess

#check (@CoveringDesigns.C14_5_3.residual_marks_card : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] (B : ι → Finset α) (x : α) (i : { i // x ∉ B i }),
  (CoveringDesigns.C14_5_3.residualMarks B x i).card = (B ↑i ∩ CoveringDesigns.C14_5_3.middlePoints B).card)
#guard_standard_axioms CoveringDesigns.C14_5_3.residual_marks_card
#print axioms CoveringDesigns.C14_5_3.residual_marks_card

#check (@CoveringDesigns.C14_5_3.special_charge_eight : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {x : α},
        CoveringDesigns.indexedDegree B x = 13 →
          ∀ (i : { i // x ∉ B i }),
            (B ↑i ∩ CoveringDesigns.C14_5_3.middlePoints B).card = 2 →
              8 ≤
                CoveringDesigns.C14_5_3.collinearCount (CoveringDesigns.Multicover.subsetLink B {x})
                      (CoveringDesigns.C14_5_3.residualBlocks B x i) -
                    1 +
                  (CoveringDesigns.C14_5_3.chargedTriples (CoveringDesigns.Multicover.subsetLink B {x})
                      (CoveringDesigns.C14_5_3.residualBlocks B x i) (CoveringDesigns.C14_5_3.residualMarks B x i)).card)
#guard_standard_axioms CoveringDesigns.C14_5_3.special_charge_eight
#print axioms CoveringDesigns.C14_5_3.special_charge_eight

#check (@CoveringDesigns.C14_5_3.minimum_special_count : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      Fintype.card ι = 40 →
        ∀ {x : α}, CoveringDesigns.indexedDegree B x = 13 → (CoveringDesigns.C14_5_3.specialIndices B).card ≤ 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.minimum_special_count
#print axioms CoveringDesigns.C14_5_3.minimum_special_count

#check (@CoveringDesigns.C14_5_3.without_point_card : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α] (T : Finset α),
  ∀ x ∈ T, (Finset.subtype (fun x_1 => x_1 ∉ ({x} : Finset α)) T).card = T.card - 1)
#guard_standard_axioms CoveringDesigns.C14_5_3.without_point_card
#print axioms CoveringDesigns.C14_5_3.without_point_card

#check (@CoveringDesigns.C14_5_3.insert_without_point : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α] (T : Finset α),
  ∀ x ∈ T,
    {x} ∪ Finset.map (Function.Embedding.subtype fun x_1 => x_1 ∉ ({x} : Finset α)) (Finset.subtype (fun x_1 => x_1 ∉ ({x} : Finset α)) T) = T)
#guard_standard_axioms CoveringDesigns.C14_5_3.insert_without_point
#print axioms CoveringDesigns.C14_5_3.insert_without_point

#check (@CoveringDesigns.C14_5_3.link_parent_multiplicity : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (T : Finset α),
  ∀ x ∈ T,
    CoveringDesigns.indexedSubsetDegree (CoveringDesigns.Multicover.subsetLink B {x})
        (Finset.subtype (fun x_1 => x_1 ∉ ({x} : Finset α)) T) =
      CoveringDesigns.indexedSubsetDegree B T)
#guard_standard_axioms CoveringDesigns.C14_5_3.link_parent_multiplicity
#print axioms CoveringDesigns.C14_5_3.link_parent_multiplicity

#check (@CoveringDesigns.C14_5_3.without_point_subset_iff : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (S T : Finset α),
  ∀ x ∈ S, x ∈ T → (Finset.subtype (fun x_1 => x_1 ∉ ({x} : Finset α)) S ⊆ Finset.subtype (fun x_1 => x_1 ∉ ({x} : Finset α)) T ↔ S ⊆ T))
#guard_standard_axioms CoveringDesigns.C14_5_3.without_point_subset_iff
#print axioms CoveringDesigns.C14_5_3.without_point_subset_iff

#check (@CoveringDesigns.C14_5_3.exists_special : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {x : α}, CoveringDesigns.indexedDegree B x = 14 → ∃ i, CoveringDesigns.C14_5_3.SpecialAt B x i)
#guard_standard_axioms CoveringDesigns.C14_5_3.exists_special
#print axioms CoveringDesigns.C14_5_3.exists_special

#check (@CoveringDesigns.C14_5_3.SpecialAt.duplicate : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] {B : ι → Finset α} {x : α} {i : ι},
  CoveringDesigns.C14_5_3.SpecialAt B x i →
    ∀ {T : Finset α}, T.card = 3 → x ∈ T → T ⊆ B i → CoveringDesigns.indexedSubsetDegree B T = 2)
#guard_standard_axioms CoveringDesigns.C14_5_3.SpecialAt.duplicate
#print axioms CoveringDesigns.C14_5_3.SpecialAt.duplicate

#check (@CoveringDesigns.C14_5_3.special_blocks_equal : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [inst_1 : Fintype ι] {B : ι → Finset α},
  CoveringDesigns.Multicover.Uniform B 5 →
    ∀ {x y : α} {i j : ι},
      CoveringDesigns.C14_5_3.SpecialAt B x i → CoveringDesigns.C14_5_3.SpecialAt B y j → y ∈ B i → B i = B j)
#guard_standard_axioms CoveringDesigns.C14_5_3.special_blocks_equal
#print axioms CoveringDesigns.C14_5_3.special_blocks_equal

#check (@CoveringDesigns.C14_5_3.special_avoids_minimum : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      ∀ {x y : α} {i : ι},
        CoveringDesigns.indexedDegree B x = 14 →
          CoveringDesigns.C14_5_3.SpecialAt B x i → CoveringDesigns.indexedDegree B y = 13 → y ∉ B i)
#guard_standard_axioms CoveringDesigns.C14_5_3.special_avoids_minimum
#print axioms CoveringDesigns.C14_5_3.special_avoids_minimum

#check (@CoveringDesigns.C14_5_3.mem_specialIndices : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α} {i : ι},
  i ∈ CoveringDesigns.C14_5_3.specialIndices B ↔
    ∃ x, CoveringDesigns.indexedDegree B x = 14 ∧ CoveringDesigns.C14_5_3.SpecialAt B x i)
#guard_standard_axioms CoveringDesigns.C14_5_3.mem_specialIndices
#print axioms CoveringDesigns.C14_5_3.mem_specialIndices

#check (@CoveringDesigns.C14_5_3.special_at_member : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      CoveringDesigns.C14_5_3.Irredundant B 3 →
        ∀ {i : ι},
          i ∈ CoveringDesigns.C14_5_3.specialIndices B →
            ∀ {y : α}, CoveringDesigns.indexedDegree B y = 14 → y ∈ B i → CoveringDesigns.C14_5_3.SpecialAt B y i)
#guard_standard_axioms CoveringDesigns.C14_5_3.special_at_member
#print axioms CoveringDesigns.C14_5_3.special_at_member

#check (@CoveringDesigns.C14_5_3.special_group_unique : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      CoveringDesigns.C14_5_3.Irredundant B 3 →
        ∀ {i j : ι},
          i ∈ CoveringDesigns.C14_5_3.specialIndices B →
            j ∈ CoveringDesigns.C14_5_3.specialIndices B →
              ∀ {y : α}, CoveringDesigns.indexedDegree B y = 14 → y ∈ B i → y ∈ B j → i = j)
#guard_standard_axioms CoveringDesigns.C14_5_3.special_group_unique
#print axioms CoveringDesigns.C14_5_3.special_group_unique

#check (@CoveringDesigns.C14_5_3.private_high : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α]
  [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      CoveringDesigns.C14_5_3.Irredundant B 3 →
        ∀ {i : ι},
          i ∈ CoveringDesigns.C14_5_3.specialIndices B →
            ∀ {T : Finset α},
              T.card = 3 →
                T ⊆ B i → CoveringDesigns.indexedSubsetDegree B T = 1 → T ⊆ CoveringDesigns.C14_5_3.highPoints B)
#guard_standard_axioms CoveringDesigns.C14_5_3.private_high
#print axioms CoveringDesigns.C14_5_3.private_high

#check (@CoveringDesigns.C14_5_3.special_middle_le_two : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      CoveringDesigns.C14_5_3.Irredundant B 3 →
        ∀ {i : ι},
          i ∈ CoveringDesigns.C14_5_3.specialIndices B → (B i ∩ CoveringDesigns.C14_5_3.middlePoints B).card ≤ 2)
#guard_standard_axioms CoveringDesigns.C14_5_3.special_middle_le_two
#print axioms CoveringDesigns.C14_5_3.special_middle_le_two

#check (@CoveringDesigns.C14_5_3.selected_intersection_sum : ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [inst : DecidableEq α]
  [Fintype ι] [DecidableEq ι] (B : ι → Finset α) (S : Finset ι) (H : Finset α),
  ∑ i ∈ S, (B i ∩ H).card = ∑ x ∈ H, {i ∈ S | x ∈ B i}.card)
#guard_standard_axioms CoveringDesigns.C14_5_3.selected_intersection_sum
#print axioms CoveringDesigns.C14_5_3.selected_intersection_sum

#check (@CoveringDesigns.C14_5_3.special_group_count : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      CoveringDesigns.C14_5_3.Irredundant B 3 →
        ∑ i ∈ CoveringDesigns.C14_5_3.specialIndices B, (B i ∩ CoveringDesigns.C14_5_3.middlePoints B).card =
          (CoveringDesigns.C14_5_3.middlePoints B).card)
#guard_standard_axioms CoveringDesigns.C14_5_3.special_group_count
#print axioms CoveringDesigns.C14_5_3.special_group_count

#check (@CoveringDesigns.C14_5_3.middle_le_twice_special : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      CoveringDesigns.C14_5_3.Irredundant B 3 →
        (CoveringDesigns.C14_5_3.middlePoints B).card ≤ 2 * (CoveringDesigns.C14_5_3.specialIndices B).card)
#guard_standard_axioms CoveringDesigns.C14_5_3.middle_le_twice_special
#print axioms CoveringDesigns.C14_5_3.middle_le_twice_special

#check (@CoveringDesigns.C14_5_3.distinct_private_triples : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 14 →
    CoveringDesigns.Multicover.IsCover B 5 3 1 →
      CoveringDesigns.C14_5_3.Irredundant B 3 →
        (CoveringDesigns.C14_5_3.specialIndices B).card ≤ (CoveringDesigns.C14_5_3.highPoints B).card.choose 3)
#guard_standard_axioms CoveringDesigns.C14_5_3.distinct_private_triples
#print axioms CoveringDesigns.C14_5_3.distinct_private_triples

#check (@CoveringDesigns.knownBlocks43_14_5_3_distinct : CoveringDesigns.knownBlocks43_14_5_3.Nodup)
#guard_standard_axioms CoveringDesigns.knownBlocks43_14_5_3_distinct
#print axioms CoveringDesigns.knownBlocks43_14_5_3_distinct

#check (@CoveringDesigns.knownCover43_14_5_3_card : Finset.card CoveringDesigns.knownCover43_14_5_3 = 43)
#guard_standard_axioms CoveringDesigns.knownCover43_14_5_3_card
#print axioms CoveringDesigns.knownCover43_14_5_3_card

#check (@CoveringDesigns.knownCover43_14_5_3_uniform : CoveringDesigns.Uniform CoveringDesigns.knownCover43_14_5_3 5)
#guard_standard_axioms CoveringDesigns.knownCover43_14_5_3_uniform
#print axioms CoveringDesigns.knownCover43_14_5_3_uniform

#check (@CoveringDesigns.knownCover43_14_5_3_covers : CoveringDesigns.Covers CoveringDesigns.knownCover43_14_5_3 3)
#guard_standard_axioms CoveringDesigns.knownCover43_14_5_3_covers
#print axioms CoveringDesigns.knownCover43_14_5_3_covers

#check (@CoveringDesigns.knownCover43_14_5_3_isCover : CoveringDesigns.IsCover CoveringDesigns.knownCover43_14_5_3 5 3)
#guard_standard_axioms CoveringDesigns.knownCover43_14_5_3_isCover
#print axioms CoveringDesigns.knownCover43_14_5_3_isCover

#check (@CoveringDesigns.upper_bound_14_5_3 : ∃ C, CoveringDesigns.IsCover C 5 3 ∧ Finset.card C = 43)
#guard_standard_axioms CoveringDesigns.upper_bound_14_5_3
#print axioms CoveringDesigns.upper_bound_14_5_3

#check (@CoveringDesigns.knownCover43_14_5_3_on_card : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (hv : Fintype.card α = 14), Finset.card (CoveringDesigns.knownCover43_14_5_3_on hv) = 43)
#guard_standard_axioms CoveringDesigns.knownCover43_14_5_3_on_card
#print axioms CoveringDesigns.knownCover43_14_5_3_on_card

#check (@CoveringDesigns.knownCover43_14_5_3_on_isCover : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (hv : Fintype.card α = 14), CoveringDesigns.IsCover (CoveringDesigns.knownCover43_14_5_3_on hv) 5 3)
#guard_standard_axioms CoveringDesigns.knownCover43_14_5_3_on_isCover
#print axioms CoveringDesigns.knownCover43_14_5_3_on_isCover

#check (@CoveringDesigns.upper_bound_14_5_3_on : ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α],
  Fintype.card α = 14 → ∃ C, CoveringDesigns.IsCover C 5 3 ∧ Finset.card C = 43)
#guard_standard_axioms CoveringDesigns.upper_bound_14_5_3_on
#print axioms CoveringDesigns.upper_bound_14_5_3_on

#check (@CoveringDesigns.lower_bound_14_5_3 : ∀ {α : Type u_1} [inst : Fintype α] {C : CoveringDesigns.Family α},
  Fintype.card α = 14 → CoveringDesigns.IsCover C 5 3 → 41 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.lower_bound_14_5_3
#print axioms CoveringDesigns.lower_bound_14_5_3

#check (@CoveringDesigns.indexed_lower_bound_14_5_3 : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  (B : ι → Finset α),
  Fintype.card α = 14 →
    (∀ (i : ι), (B i).card = 5) → (∀ (T : Finset α), T.card = 3 → ∃ i, T ⊆ B i) → 41 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.indexed_lower_bound_14_5_3
#print axioms CoveringDesigns.indexed_lower_bound_14_5_3

#check (@CoveringDesigns.covering_interval_14_5_3_on : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 14 →
    (∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 5 3 → 41 ≤ Finset.card C) ∧
      ∃ C, CoveringDesigns.IsCover C 5 3 ∧ Finset.card C = 43)
#guard_standard_axioms CoveringDesigns.covering_interval_14_5_3_on
#print axioms CoveringDesigns.covering_interval_14_5_3_on

#check (@CoveringDesigns.covering_interval_14_5_3 : (∀ (C : CoveringDesigns.Family (Fin 14)),
    CoveringDesigns.IsCover C 5 3 → 41 ≤ Finset.card C) ∧
  ∃ C, CoveringDesigns.IsCover C 5 3 ∧ Finset.card C = 43)
#guard_standard_axioms CoveringDesigns.covering_interval_14_5_3
#print axioms CoveringDesigns.covering_interval_14_5_3

#guard_standard_axioms CoveringDesigns.Audit14_5_3.covering_interval_explicit
#print axioms CoveringDesigns.Audit14_5_3.covering_interval_explicit

#guard_standard_axioms CoveringDesigns.Audit14_5_3.indexed_explicit
#print axioms CoveringDesigns.Audit14_5_3.indexed_explicit

#guard_standard_axioms CoveringDesigns.Audit14_5_3.completion_explicit
#print axioms CoveringDesigns.Audit14_5_3.completion_explicit
