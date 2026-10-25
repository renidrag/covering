import CoveringDesigns.ProjectiveLinkBounds
import CoveringDesigns.Foundations.StandardAxioms

/-! Frozen full contracts, explicit covering hypotheses and transitive axiom guards.
Internal cross-module bookkeeping is checked too; it is not a supported API. -/
open Finset
open scoped BigOperators
universe u_1 u_2
set_option linter.unusedVariables false

namespace CoveringDesigns.AuditProjectiveLinkBounds
open ProjectiveLinkBounds

-- Only cardinality, uniformity and coverage remain in these contracts.
theorem indexed_explicit {α : Type u_1} {ι : Type u_2}
    [Fintype α] [DecidableEq α] [Fintype ι] {q : ℕ}
    (hq : 3 ≤ q) (ho : Odd q) (B : ι → Finset α)
    (hv : Fintype.card α = q^2+q+2)
    (hu : ∀ i, (B i).card = q+2)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) :
    min (Schoenheim.ceilDiv ((q^2+q+2)*(q^2+q+3)) (q+2))
      (q^2+q+1 + Schoenheim.ceilDiv ((q^2+q+1)*q^3*(q+1)/6)
        ((q+2).choose 3 - Schoenheim.ceilDiv q 4)) ≤ Fintype.card ι := by
  simpa only [familyBound, pointCount, tripleDemand, capacity, collinearFloor,
    Nat.add_assoc] using indexed_lower_bound hq ho hv
      (show Multicover.IsCover B (q+2) 3 1 from
        ⟨hu, (Multicover.covers_one_iff B 3).mpr hc⟩)

theorem ordinary_explicit {α : Type u_1} [Fintype α] [DecidableEq α]
    {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (C : Finset (Finset α))
    (hv : Fintype.card α = q^2+q+2)
    (hu : ∀ B ∈ C, B.card = q+2)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) :
    min (Schoenheim.ceilDiv ((q^2+q+2)*(q^2+q+3)) (q+2))
      (q^2+q+1 + Schoenheim.ceilDiv ((q^2+q+1)*q^3*(q+1)/6)
        ((q+2).choose 3 - Schoenheim.ceilDiv q 4)) ≤ C.card := by
  simpa only [familyBound, pointCount, tripleDemand, capacity, collinearFloor,
    Nat.add_assoc] using lower_bound hq ho hv (show IsCover C (q+2) 3 from ⟨hu,hc⟩)

theorem weak_indexed_explicit {α : Type u_1} {ι : Type u_2}
    [Fintype α] [DecidableEq α] [Fintype ι] {q : ℕ}
    (hq : 5 ≤ q) (ho : Odd q) (B : ι → Finset α)
    (hv : Fintype.card α = q^2+q+2)
    (hu : ∀ i, (B i).card = q+2)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) :
    Schoenheim.ceilDiv ((q^2+q+2)^2) (q+2) ≤ Fintype.card ι := by
  simpa only [weakBound, pointCount, Nat.add_assoc] using indexed_weak_lower_bound hq ho hv
    (show Multicover.IsCover B (q+2) 3 1 from
      ⟨hu, (Multicover.covers_one_iff B 3).mpr hc⟩)

theorem weak_ordinary_explicit {α : Type u_1} [Fintype α] [DecidableEq α]
    {q : ℕ} (hq : 5 ≤ q) (ho : Odd q) (C : Finset (Finset α))
    (hv : Fintype.card α = q^2+q+2)
    (hu : ∀ B ∈ C, B.card = q+2)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) :
    Schoenheim.ceilDiv ((q^2+q+2)^2) (q+2) ≤ C.card := by
  simpa only [weakBound, pointCount, Nat.add_assoc] using weak_lower_bound hq ho hv
    (show IsCover C (q+2) 3 from ⟨hu,hc⟩)

#guard_standard_axioms indexed_explicit
#print axioms indexed_explicit
#guard_standard_axioms ordinary_explicit
#print axioms ordinary_explicit
#guard_standard_axioms weak_indexed_explicit
#print axioms weak_indexed_explicit
#guard_standard_axioms weak_ordinary_explicit
#print axioms weak_ordinary_explicit

end CoveringDesigns.AuditProjectiveLinkBounds

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.Multicover.Uniform
#print CoveringDesigns.Multicover.Covers
#print CoveringDesigns.Multicover.IsCover
#print CoveringDesigns.ExactDesign.IsDesign
#print CoveringDesigns.indexedSubsetDegree
#print CoveringDesigns.Schoenheim.ceilDiv
#print CoveringDesigns.ProjectiveLinkBounds.pointCount
#print CoveringDesigns.ProjectiveLinkBounds.collinearFloor
#print CoveringDesigns.ProjectiveLinkBounds.tripleDemand
#print CoveringDesigns.ProjectiveLinkBounds.capacity
#print CoveringDesigns.ProjectiveLinkBounds.familyBound
#print CoveringDesigns.ProjectiveLinkBounds.weakBound
#print CoveringDesigns.ProjectiveLinkBounds.collinearTriples
#print CoveringDesigns.ProjectiveLinkBounds.noncollinearTriples
#print CoveringDesigns.ProjectiveLinkBounds.pointTrace

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.choose_two_int :
  ∀ (m : ℕ),
  2 * (↑(m.choose 2) : ℤ) = (↑m : ℤ) * ((↑m : ℤ) - 1))
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.choose_two_int
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.choose_two_int

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.choose_three_int :
  ∀ (m : ℕ),
  6 * (↑(m.choose 3) : ℤ) = (↑m : ℤ) * ((↑m : ℤ) - 1) * ((↑m : ℤ) - 2))
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.choose_three_int
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.choose_three_int

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.floor_bounds :
  ∀ {q : ℕ},
  Odd q →
    q + 1 ≤ 4 * CoveringDesigns.ProjectiveLinkBounds.collinearFloor q ∧
      4 * CoveringDesigns.ProjectiveLinkBounds.collinearFloor q ≤ q + 3)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.floor_bounds
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.floor_bounds

#check (@CoveringDesigns.ProjectiveLinkBounds.collinearFloor_eq :
  ∀ {q : ℕ},
  3 ≤ q →
    Odd q →
      CoveringDesigns.Schoenheim.ceilDiv (q ^ 2 - 1) (4 * q - 2) = CoveringDesigns.ProjectiveLinkBounds.collinearFloor q)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.collinearFloor_eq
#print axioms CoveringDesigns.ProjectiveLinkBounds.collinearFloor_eq

#check (@CoveringDesigns.ProjectiveLinkBounds.capacity_ge :
  ∀ {q : ℕ},
  3 ≤ q → (q + 1).choose 3 ≤ CoveringDesigns.ProjectiveLinkBounds.capacity q)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.capacity_ge
#print axioms CoveringDesigns.ProjectiveLinkBounds.capacity_ge

#check (@CoveringDesigns.ProjectiveLinkBounds.capacity_pos :
  ∀ {q : ℕ},
  3 ≤ q → 0 < CoveringDesigns.ProjectiveLinkBounds.capacity q)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.capacity_pos
#print axioms CoveringDesigns.ProjectiveLinkBounds.capacity_pos

#check (@CoveringDesigns.ProjectiveLinkBounds.capacity_balance :
  ∀ {q : ℕ},
  3 ≤ q →
    CoveringDesigns.ProjectiveLinkBounds.capacity q + CoveringDesigns.ProjectiveLinkBounds.collinearFloor q =
      (q + 2).choose 3)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.capacity_balance
#print axioms CoveringDesigns.ProjectiveLinkBounds.capacity_balance

#check (@CoveringDesigns.ProjectiveLinkBounds.demand_balance :
  ∀ (q : ℕ),
  CoveringDesigns.ProjectiveLinkBounds.tripleDemand q +
      CoveringDesigns.ProjectiveLinkBounds.pointCount q * (q + 1).choose 3 =
    (CoveringDesigns.ProjectiveLinkBounds.pointCount q).choose 3)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.demand_balance
#print axioms CoveringDesigns.ProjectiveLinkBounds.demand_balance

#check (@CoveringDesigns.ProjectiveLinkBounds.demand_six :
  ∀ (q : ℕ),
  6 * CoveringDesigns.ProjectiveLinkBounds.tripleDemand q =
    CoveringDesigns.ProjectiveLinkBounds.pointCount q * q ^ 3 * (q + 1))
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.demand_six
#print axioms CoveringDesigns.ProjectiveLinkBounds.demand_six

#check (@CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  3 ≤ q →
    Odd q →
      ∀ {B : ι → Finset α},
        Fintype.card α = q ^ 2 + q + 2 →
          CoveringDesigns.Multicover.IsCover B (q + 2) 3 1 →
            CoveringDesigns.ProjectiveLinkBounds.familyBound q ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound
#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound

#check (@CoveringDesigns.ProjectiveLinkBounds.lower_bound :
  ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α] {q : ℕ},
  3 ≤ q →
    Odd q →
      ∀ {C : CoveringDesigns.Family α},
        Fintype.card α = q ^ 2 + q + 2 →
          CoveringDesigns.IsCover C (q + 2) 3 → CoveringDesigns.ProjectiveLinkBounds.familyBound q ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.lower_bound
#print axioms CoveringDesigns.ProjectiveLinkBounds.lower_bound

#check (@CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound_32_7_3 :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 32 → CoveringDesigns.Multicover.IsCover B 7 3 1 → 149 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound_32_7_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound_32_7_3

#check (@CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound_58_9_3 :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 58 → CoveringDesigns.Multicover.IsCover B 9 3 1 → 375 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound_58_9_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound_58_9_3

#check (@CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound_92_11_3 :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 92 → CoveringDesigns.Multicover.IsCover B 11 3 1 → 774 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound_92_11_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_lower_bound_92_11_3

#check (@CoveringDesigns.ProjectiveLinkBounds.lower_bound_32_7_3 :
  ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 32 → CoveringDesigns.IsCover C 7 3 → 149 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.lower_bound_32_7_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.lower_bound_32_7_3

#check (@CoveringDesigns.ProjectiveLinkBounds.lower_bound_58_9_3 :
  ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 58 → CoveringDesigns.IsCover C 9 3 → 375 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.lower_bound_58_9_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.lower_bound_58_9_3

#check (@CoveringDesigns.ProjectiveLinkBounds.lower_bound_92_11_3 :
  ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 92 → CoveringDesigns.IsCover C 11 3 → 774 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.lower_bound_92_11_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.lower_bound_92_11_3

#check (@CoveringDesigns.ProjectiveLinkBounds.indexed_weak_bound_32_7_3 :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 32 → CoveringDesigns.Multicover.IsCover B 7 3 1 → 147 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_bound_32_7_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_bound_32_7_3

#check (@CoveringDesigns.ProjectiveLinkBounds.indexed_weak_bound_58_9_3 :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 58 → CoveringDesigns.Multicover.IsCover B 9 3 1 → 374 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_bound_58_9_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_bound_58_9_3

#check (@CoveringDesigns.ProjectiveLinkBounds.indexed_weak_bound_92_11_3 :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {B : ι → Finset α},
  Fintype.card α = 92 → CoveringDesigns.Multicover.IsCover B 11 3 1 → 770 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_bound_92_11_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_bound_92_11_3

#check (@CoveringDesigns.ProjectiveLinkBounds.weak_bound_32_7_3 :
  ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 32 → CoveringDesigns.IsCover C 7 3 → 147 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.weak_bound_32_7_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.weak_bound_32_7_3

#check (@CoveringDesigns.ProjectiveLinkBounds.weak_bound_58_9_3 :
  ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 58 → CoveringDesigns.IsCover C 9 3 → 374 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.weak_bound_58_9_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.weak_bound_58_9_3

#check (@CoveringDesigns.ProjectiveLinkBounds.weak_bound_92_11_3 :
  ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 92 → CoveringDesigns.IsCover C 11 3 → 770 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.weak_bound_92_11_3
#print axioms CoveringDesigns.ProjectiveLinkBounds.weak_bound_92_11_3

#check (@CoveringDesigns.ProjectiveLinkBounds.calibration_three :
  CoveringDesigns.ProjectiveLinkBounds.familyBound 3 = 39)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.calibration_three
#print axioms CoveringDesigns.ProjectiveLinkBounds.calibration_three

#check (@CoveringDesigns.ProjectiveLinkBounds.noncollinear_card :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  3 ≤ q →
    ∀ {L : ι → Finset α},
      Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
        CoveringDesigns.ExactDesign.IsDesign L (q + 1) 2 1 →
          (CoveringDesigns.ProjectiveLinkBounds.noncollinearTriples L).card =
            CoveringDesigns.ProjectiveLinkBounds.tripleDemand q)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.noncollinear_card
#print axioms CoveringDesigns.ProjectiveLinkBounds.noncollinear_card

#check (@CoveringDesigns.ProjectiveLinkBounds.completion_count :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  3 ≤ q →
    Odd q →
      ∀ {B : ι → Finset α},
        Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q + 1 →
          CoveringDesigns.Multicover.IsCover B (q + 2) 3 1 →
            ∀ (x : α) (J : Finset ι),
              (∀ j ∈ J, x ∈ B j) →
                CoveringDesigns.ExactDesign.IsDesign
                    (fun (j : ↥J) => CoveringDesigns.ProjectiveLinkBounds.pointTrace B x (↑j : ι)) (q + 1) 2 1 →
                  CoveringDesigns.ProjectiveLinkBounds.tripleDemand q ≤
                    (Fintype.card ι - CoveringDesigns.ProjectiveLinkBounds.pointCount q) *
                      CoveringDesigns.ProjectiveLinkBounds.capacity q)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.completion_count
#print axioms CoveringDesigns.ProjectiveLinkBounds.completion_count

#check (@CoveringDesigns.ProjectiveLinkBounds.completion_bound :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  3 ≤ q →
    Odd q →
      ∀ {B : ι → Finset α},
        Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q + 1 →
          CoveringDesigns.Multicover.IsCover B (q + 2) 3 1 →
            ∀ (x : α) (J : Finset ι),
              (∀ j ∈ J, x ∈ B j) →
                CoveringDesigns.ExactDesign.IsDesign
                    (fun (j : ↥J) => CoveringDesigns.ProjectiveLinkBounds.pointTrace B x (↑j : ι)) (q + 1) 2 1 →
                  CoveringDesigns.ProjectiveLinkBounds.pointCount q +
                      CoveringDesigns.Schoenheim.ceilDiv (CoveringDesigns.ProjectiveLinkBounds.tripleDemand q)
                        (CoveringDesigns.ProjectiveLinkBounds.capacity q) ≤
                    Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.completion_bound
#print axioms CoveringDesigns.ProjectiveLinkBounds.completion_bound

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.completion_of_link_selection :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : Fintype α] [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  3 ≤ q →
    Odd q →
      ∀ {B : ι → Finset α},
        Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q + 1 →
          CoveringDesigns.Multicover.IsCover B (q + 2) 3 1 →
            ∀ (x : α) (K : Finset { i : ι // {x} ⊆ B i }),
              CoveringDesigns.ExactDesign.IsDesign
                  (fun (j : ↥K) => CoveringDesigns.Multicover.subsetLink B {x} (↑j : { i : ι // {x} ⊆ B i })) (q + 1) 2
                  1 →
                CoveringDesigns.ProjectiveLinkBounds.tripleDemand q ≤
                    (Fintype.card ι - CoveringDesigns.ProjectiveLinkBounds.pointCount q) *
                      CoveringDesigns.ProjectiveLinkBounds.capacity q ∧
                  CoveringDesigns.ProjectiveLinkBounds.pointCount q +
                      CoveringDesigns.Schoenheim.ceilDiv (CoveringDesigns.ProjectiveLinkBounds.tripleDemand q)
                        (CoveringDesigns.ProjectiveLinkBounds.capacity q) ≤
                    Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.completion_of_link_selection
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.completion_of_link_selection

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.completion_of_exact_link :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : Fintype α] [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  3 ≤ q →
    Odd q →
      ∀ {B : ι → Finset α},
        Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q + 1 →
          CoveringDesigns.Multicover.IsCover B (q + 2) 3 1 →
            ∀ (x : α),
              CoveringDesigns.indexedDegree B x = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
                CoveringDesigns.ProjectiveLinkBounds.tripleDemand q ≤
                    (Fintype.card ι - CoveringDesigns.ProjectiveLinkBounds.pointCount q) *
                      CoveringDesigns.ProjectiveLinkBounds.capacity q ∧
                  CoveringDesigns.ProjectiveLinkBounds.pointCount q +
                      CoveringDesigns.Schoenheim.ceilDiv (CoveringDesigns.ProjectiveLinkBounds.tripleDemand q)
                        (CoveringDesigns.ProjectiveLinkBounds.capacity q) ≤
                    Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.completion_of_exact_link
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.completion_of_exact_link

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.parent_degree_floor :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  3 ≤ q →
    ∀ {B : ι → Finset α},
      Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q + 1 →
        CoveringDesigns.Multicover.IsCover B (q + 2) 3 1 →
          ∀ (x : α), CoveringDesigns.ProjectiveLinkBounds.pointCount q ≤ CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.parent_degree_floor
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.parent_degree_floor

#check (@CoveringDesigns.ProjectiveLinkBounds.furedi_sane_deletion :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  2 ≤ q →
    ∀ {B : ι → Finset α},
      Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
        CoveringDesigns.Multicover.IsCover B (q + 1) 2 1 →
          Fintype.card ι = CoveringDesigns.ProjectiveLinkBounds.pointCount q + 1 →
            ∃ (J : Finset ι),
              J.card = CoveringDesigns.ProjectiveLinkBounds.pointCount q ∧
                CoveringDesigns.ExactDesign.IsDesign (fun (j : ↥J) => B (↑j : ι)) (q + 1) 2 1)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.furedi_sane_deletion
#print axioms CoveringDesigns.ProjectiveLinkBounds.furedi_sane_deletion

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.multiplicity_mono :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : DecidableEq α] [inst_1 : Fintype ι] (B : ι → Finset α) {S T : Finset α},
  S ⊆ T → CoveringDesigns.indexedSubsetDegree B T ≤ CoveringDesigns.indexedSubsetDegree B S)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.multiplicity_mono
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.multiplicity_mono

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.multiplicity_pos_iff :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : DecidableEq α] [inst_1 : Fintype ι] (B : ι → Finset α) (T : Finset α),
  0 < CoveringDesigns.indexedSubsetDegree B T ↔ ∃ (i : ι), T ⊆ B i)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.multiplicity_pos_iff
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.multiplicity_pos_iff

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.multiplicity_ge_two :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : DecidableEq α] [inst_1 : Fintype ι] (B : ι → Finset α) {T : Finset α} {i j : ι},
  i ≠ j → T ⊆ B i → T ⊆ B j → 2 ≤ CoveringDesigns.indexedSubsetDegree B T)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.multiplicity_ge_two
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.multiplicity_ge_two

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.trace_count :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (S : Finset α) (r : ℕ),
  ∑ T ∈ Finset.powersetCard r S, CoveringDesigns.indexedSubsetDegree B T = ∑ i : ι, (B i ∩ S).card.choose r)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.trace_count
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.trace_count

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.intersection_sum :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] (B : ι → Finset α) (S : Finset α),
  ∑ i : ι, (B i ∩ S).card = ∑ x ∈ S, CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.intersection_sum
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.intersection_sum

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.selected_subset_count :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : DecidableEq α] [inst_1 : Fintype ι] (B : ι → Finset α) (A : Finset (Finset α)),
  ∑ T ∈ A, CoveringDesigns.indexedSubsetDegree B T = ∑ i : ι, {x ∈ A | x ⊆ B i}.card)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.selected_subset_count
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.selected_subset_count

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.restrict_multiplicity :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : DecidableEq α] [inst_1 : Fintype ι] (B : ι → Finset α) (p : ι → Prop) [inst_2 : DecidablePred p]
  [inst_3 : Fintype { i : ι // p i }] (T : Finset α),
  CoveringDesigns.indexedSubsetDegree (fun (i : { i : ι // p i }) => B (↑i : ι)) T =
    ((Finset.univ : Finset ι).filter (fun i => p i ∧ T ⊆ B i)).card)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.restrict_multiplicity
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.restrict_multiplicity

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.degree_through_point :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : DecidableEq α] [inst_1 : Fintype ι] (B : ι → Finset α) (p x : α),
  CoveringDesigns.indexedDegree (fun (i : { i : ι // p ∈ B i }) => B (↑i : ι)) x =
    CoveringDesigns.indexedSubsetDegree B {p, x})
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.degree_through_point
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.degree_through_point

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.pair_point_floor :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] [inst_2 : Fintype α] {B : ι → Finset α} {q : ℕ},
  1 ≤ q →
    Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
      CoveringDesigns.Multicover.IsCover B (q + 1) 2 1 → ∀ (x : α), q + 1 ≤ CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.pair_point_floor
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.pair_point_floor

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.regular_pair :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] [inst_2 : Fintype α] {B : ι → Finset α} {q : ℕ},
  Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
    CoveringDesigns.Multicover.IsCover B (q + 1) 2 1 →
      ∀ {x y : α}, CoveringDesigns.indexedDegree B x = q + 1 → x ≠ y → CoveringDesigns.indexedSubsetDegree B {x, y} = 1)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.regular_pair
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.regular_pair

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.pair_cover_lower :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] [inst_2 : Fintype α] {B : ι → Finset α} {q : ℕ},
  1 ≤ q →
    Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
      CoveringDesigns.Multicover.IsCover B (q + 1) 2 1 →
        CoveringDesigns.ProjectiveLinkBounds.pointCount q ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.pair_cover_lower
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.pair_cover_lower

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.pair_cover_exact :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] [inst_2 : Fintype α] {B : ι → Finset α} {q : ℕ},
  1 ≤ q →
    Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
      CoveringDesigns.Multicover.IsCover B (q + 1) 2 1 →
        Fintype.card ι = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
          CoveringDesigns.ExactDesign.IsDesign B (q + 1) 2 1)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.pair_cover_exact
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.pair_cover_exact

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.exact_point_count :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : DecidableEq α] [inst_1 : Fintype ι] [inst_2 : Fintype α] {L : ι → Finset α} {q : ℕ},
  1 ≤ q →
    Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
      CoveringDesigns.ExactDesign.IsDesign L (q + 1) 2 1 → ∀ (x : α), CoveringDesigns.indexedDegree L x = q + 1)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.exact_point_count
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.exact_point_count

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.exact_line_count :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq α]
  [inst_1 : Fintype ι] [inst_2 : Fintype α] {L : ι → Finset α} {q : ℕ},
  1 ≤ q →
    Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
      CoveringDesigns.ExactDesign.IsDesign L (q + 1) 2 1 →
        Fintype.card ι = CoveringDesigns.ProjectiveLinkBounds.pointCount q)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.exact_line_count
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.exact_line_count

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.exact_multiplicity_le_one :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : DecidableEq α] [inst_1 : Fintype ι] {L : ι → Finset α} {q : ℕ},
  CoveringDesigns.ExactDesign.IsDesign L (q + 1) 2 1 →
    ∀ {T : Finset α}, 2 ≤ T.card → CoveringDesigns.indexedSubsetDegree L T ≤ 1)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.exact_multiplicity_le_one
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.exact_multiplicity_le_one

#check (@CoveringDesigns.ProjectiveLinkBounds.Internal.exact_line_intersection :
  ∀ {α : Type u_1} {ι : Type u_2}
  [inst : DecidableEq α] [inst_1 : Fintype ι] {L : ι → Finset α} {q : ℕ},
  CoveringDesigns.ExactDesign.IsDesign L (q + 1) 2 1 → ∀ {i j : ι}, i ≠ j → (L i ∩ L j).card ≤ 1)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.Internal.exact_line_intersection
#print axioms CoveringDesigns.ProjectiveLinkBounds.Internal.exact_line_intersection

#check (@CoveringDesigns.ProjectiveLinkBounds.collinear_count :
  ∀ {α : Type u_1} {ι : Type u_2} [Fintype α]
  [inst : DecidableEq α] [inst_1 : Fintype ι] {L : ι → Finset α} {q : ℕ},
  CoveringDesigns.ExactDesign.IsDesign L (q + 1) 2 1 →
    ∀ (A : Finset α),
      (CoveringDesigns.ProjectiveLinkBounds.collinearTriples L A).card = ∑ i : ι, (L i ∩ A).card.choose 3)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.collinear_count
#print axioms CoveringDesigns.ProjectiveLinkBounds.collinear_count

#check (@CoveringDesigns.ProjectiveLinkBounds.parity_bound :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  3 ≤ q →
    Odd q →
      ∀ {L : ι → Finset α},
        Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
          CoveringDesigns.ExactDesign.IsDesign L (q + 1) 2 1 →
            ∀ {A : Finset α},
              A.card = q + 2 →
                q ^ 2 - 1 ≤ (4 * q - 2) * (CoveringDesigns.ProjectiveLinkBounds.collinearTriples L A).card)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.parity_bound
#print axioms CoveringDesigns.ProjectiveLinkBounds.parity_bound

#check (@CoveringDesigns.ProjectiveLinkBounds.collinear_lower_bound :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  3 ≤ q →
    Odd q →
      ∀ {L : ι → Finset α},
        Fintype.card α = CoveringDesigns.ProjectiveLinkBounds.pointCount q →
          CoveringDesigns.ExactDesign.IsDesign L (q + 1) 2 1 →
            ∀ {A : Finset α},
              A.card = q + 2 →
                CoveringDesigns.ProjectiveLinkBounds.collinearFloor q ≤
                  (CoveringDesigns.ProjectiveLinkBounds.collinearTriples L A).card)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.collinear_lower_bound
#print axioms CoveringDesigns.ProjectiveLinkBounds.collinear_lower_bound

#check (@CoveringDesigns.ProjectiveLinkBounds.indexed_weak_lower_bound :
  ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α]
  [inst_1 : DecidableEq α] [inst_2 : Fintype ι] {q : ℕ},
  5 ≤ q →
    Odd q →
      ∀ {B : ι → Finset α},
        Fintype.card α = q ^ 2 + q + 2 →
          CoveringDesigns.Multicover.IsCover B (q + 2) 3 1 →
            CoveringDesigns.ProjectiveLinkBounds.weakBound q ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_lower_bound
#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_weak_lower_bound

#check (@CoveringDesigns.ProjectiveLinkBounds.weak_lower_bound :
  ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α] {q : ℕ},
  5 ≤ q →
    Odd q →
      ∀ {C : CoveringDesigns.Family α},
        Fintype.card α = q ^ 2 + q + 2 →
          CoveringDesigns.IsCover C (q + 2) 3 → CoveringDesigns.ProjectiveLinkBounds.weakBound q ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.weak_lower_bound
#print axioms CoveringDesigns.ProjectiveLinkBounds.weak_lower_bound


-- Direct formula; the former minimum contracts remain above unchanged.
#check (@CoveringDesigns.ProjectiveLinkBounds.familyBound_eq_completion :
  ∀ {q : ℕ}, 3 ≤ q → Odd q →
    CoveringDesigns.ProjectiveLinkBounds.familyBound q =
      CoveringDesigns.ProjectiveLinkBounds.pointCount q +
        CoveringDesigns.Schoenheim.ceilDiv
          (CoveringDesigns.ProjectiveLinkBounds.tripleDemand q)
          (CoveringDesigns.ProjectiveLinkBounds.capacity q))
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.familyBound_eq_completion
#print axioms CoveringDesigns.ProjectiveLinkBounds.familyBound_eq_completion

#check (@CoveringDesigns.ProjectiveLinkBounds.indexed_completion_lower_bound :
  ∀ {α : Type u_1} {ι : Type u_2} [Fintype α] [DecidableEq α] [Fintype ι]
    {q : ℕ}, 3 ≤ q → Odd q → ∀ {B : ι → Finset α},
    Fintype.card α = q^2+q+2 → CoveringDesigns.Multicover.IsCover B (q+2) 3 1 →
    CoveringDesigns.ProjectiveLinkBounds.pointCount q +
      CoveringDesigns.Schoenheim.ceilDiv (CoveringDesigns.ProjectiveLinkBounds.tripleDemand q)
        (CoveringDesigns.ProjectiveLinkBounds.capacity q) ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.indexed_completion_lower_bound
#print axioms CoveringDesigns.ProjectiveLinkBounds.indexed_completion_lower_bound

#check (@CoveringDesigns.ProjectiveLinkBounds.completion_lower_bound :
  ∀ {α : Type u_1} [Fintype α] [DecidableEq α] {q : ℕ}, 3 ≤ q → Odd q →
    ∀ {C : CoveringDesigns.Family α}, Fintype.card α = q^2+q+2 →
    CoveringDesigns.IsCover C (q+2) 3 →
    CoveringDesigns.ProjectiveLinkBounds.pointCount q +
      CoveringDesigns.Schoenheim.ceilDiv (CoveringDesigns.ProjectiveLinkBounds.tripleDemand q)
        (CoveringDesigns.ProjectiveLinkBounds.capacity q) ≤ C.card)
#guard_standard_axioms CoveringDesigns.ProjectiveLinkBounds.completion_lower_bound
#print axioms CoveringDesigns.ProjectiveLinkBounds.completion_lower_bound

namespace CoveringDesigns.AuditProjectiveLinkBounds
open ProjectiveLinkBounds

theorem completion_indexed_explicit {α : Type u_1} {ι : Type u_2}
    [Fintype α] [DecidableEq α] [Fintype ι] {q : ℕ}
    (hq : 3 ≤ q) (ho : Odd q) (B : ι → Finset α)
    (hv : Fintype.card α = q^2+q+2)
    (hu : ∀ i, (B i).card = q+2)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) :
    q^2+q+1 + Schoenheim.ceilDiv ((q^2+q+1)*q^3*(q+1)/6)
      ((q+2).choose 3 - Schoenheim.ceilDiv q 4) ≤ Fintype.card ι := by
  simpa only [pointCount, tripleDemand, capacity, collinearFloor] using
    indexed_completion_lower_bound hq ho hv
      (show Multicover.IsCover B (q+2) 3 1 from
        ⟨hu, (Multicover.covers_one_iff B 3).mpr hc⟩)

theorem completion_ordinary_explicit {α : Type u_1} [Fintype α] [DecidableEq α]
    {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (C : Finset (Finset α))
    (hv : Fintype.card α = q^2+q+2)
    (hu : ∀ B ∈ C, B.card = q+2)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) :
    q^2+q+1 + Schoenheim.ceilDiv ((q^2+q+1)*q^3*(q+1)/6)
      ((q+2).choose 3 - Schoenheim.ceilDiv q 4) ≤ C.card := by
  simpa only [pointCount, tripleDemand, capacity, collinearFloor] using
    completion_lower_bound hq ho hv (show IsCover C (q+2) 3 from ⟨hu,hc⟩)

#guard_standard_axioms completion_indexed_explicit
#print axioms completion_indexed_explicit
#guard_standard_axioms completion_ordinary_explicit
#print axioms completion_ordinary_explicit
end CoveringDesigns.AuditProjectiveLinkBounds
