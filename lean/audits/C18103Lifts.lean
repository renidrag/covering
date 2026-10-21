import CoveringDesigns.Applications.C18103Lifts
import CoveringDesigns.Foundations.StandardAxioms

/-! Complete arbitrary-label contracts and expanded ordinary coverage for every
corollary; all arithmetic and proofs checked by the Lean kernel. -/
open CoveringDesigns
universe u
#print CoveringDesigns.IsCover

#check (@CoveringDesigns.Applications.C18103Lifts.lower_bound : ∀ {α : Type u} [Fintype α] {C : CoveringDesigns.Family α} (s : ℕ),
    Fintype.card α = 18 + s → CoveringDesigns.IsCover C (10 + s) (3 + s) →
    CoveringDesigns.Multicover.bound 12 (18 + s) (10 + s) s ≤ C.card)
#guard_standard_axioms CoveringDesigns.Applications.C18103Lifts.lower_bound
#print axioms CoveringDesigns.Applications.C18103Lifts.lower_bound

#check (@CoveringDesigns.Applications.C18103Lifts.ceilings : CoveringDesigns.Multicover.bound 12 18 10 0 = 12 ∧
    CoveringDesigns.Multicover.bound 12 19 11 1 = 21 ∧
    CoveringDesigns.Multicover.bound 12 20 12 2 = 35 ∧
    CoveringDesigns.Multicover.bound 12 21 13 3 = 57 ∧
    CoveringDesigns.Multicover.bound 12 22 14 4 = 90 ∧
    CoveringDesigns.Multicover.bound 12 23 15 5 = 138)
#guard_standard_axioms CoveringDesigns.Applications.C18103Lifts.ceilings
#print axioms CoveringDesigns.Applications.C18103Lifts.ceilings

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

namespace CoveringDesigns.AuditC18103Lifts

theorem lower_bound_19_11_4_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 19)
    (hsize : ∀ B ∈ C, B.card = 11)
    (hcover : ∀ T : Finset α, T.card = 4 → ∃ B ∈ C, T ⊆ B) :
    21 ≤ C.card := Applications.C18103Lifts.lower_bound_19_11_4 hv ⟨hsize, hcover⟩

theorem lower_bound_20_12_5_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 20)
    (hsize : ∀ B ∈ C, B.card = 12)
    (hcover : ∀ T : Finset α, T.card = 5 → ∃ B ∈ C, T ⊆ B) :
    35 ≤ C.card := Applications.C18103Lifts.lower_bound_20_12_5 hv ⟨hsize, hcover⟩

theorem lower_bound_21_13_6_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 21)
    (hsize : ∀ B ∈ C, B.card = 13)
    (hcover : ∀ T : Finset α, T.card = 6 → ∃ B ∈ C, T ⊆ B) :
    57 ≤ C.card := Applications.C18103Lifts.lower_bound_21_13_6 hv ⟨hsize, hcover⟩

theorem lower_bound_22_14_7_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 22)
    (hsize : ∀ B ∈ C, B.card = 14)
    (hcover : ∀ T : Finset α, T.card = 7 → ∃ B ∈ C, T ⊆ B) :
    90 ≤ C.card := Applications.C18103Lifts.lower_bound_22_14_7 hv ⟨hsize, hcover⟩

theorem lower_bound_23_15_8_explicit {α : Type u} [Fintype α]
    {C : Finset (Finset α)} (hv : Fintype.card α = 23)
    (hsize : ∀ B ∈ C, B.card = 15)
    (hcover : ∀ T : Finset α, T.card = 8 → ∃ B ∈ C, T ⊆ B) :
    138 ≤ C.card := Applications.C18103Lifts.lower_bound_23_15_8 hv ⟨hsize, hcover⟩

end CoveringDesigns.AuditC18103Lifts

#guard_standard_axioms CoveringDesigns.AuditC18103Lifts.lower_bound_19_11_4_explicit
#print axioms CoveringDesigns.AuditC18103Lifts.lower_bound_19_11_4_explicit
#guard_standard_axioms CoveringDesigns.AuditC18103Lifts.lower_bound_20_12_5_explicit
#print axioms CoveringDesigns.AuditC18103Lifts.lower_bound_20_12_5_explicit
#guard_standard_axioms CoveringDesigns.AuditC18103Lifts.lower_bound_21_13_6_explicit
#print axioms CoveringDesigns.AuditC18103Lifts.lower_bound_21_13_6_explicit
#guard_standard_axioms CoveringDesigns.AuditC18103Lifts.lower_bound_22_14_7_explicit
#print axioms CoveringDesigns.AuditC18103Lifts.lower_bound_22_14_7_explicit
#guard_standard_axioms CoveringDesigns.AuditC18103Lifts.lower_bound_23_15_8_explicit
#print axioms CoveringDesigns.AuditC18103Lifts.lower_bound_23_15_8_explicit
