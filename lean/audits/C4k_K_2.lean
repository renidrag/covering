import CoveringDesigns.C4k_K_2.Examples

/-! Complete expected public types and transitive foundational axioms. -/
universe u_1 u_2 u_3

namespace CoveringDesigns.AuditC4k_K_2
/-- Raw finite-set exactness on arbitrary labels. These are all covering hypotheses. -/
theorem exactness_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hk : 8 ≤ k) (hv : Fintype.card α = 4*k) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = k) ∧
      (∀ S : Finset α, S.card = 2 → ∃ B ∈ C, S ⊆ B) ∧
      C.card = (if 4 ∣ k then 20 else 21)) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = k) →
      (∀ S : Finset α, S.card = 2 → ∃ B ∈ C, S ⊆ B) →
      (if 4 ∣ k then 20 else 21) ≤ C.card) := by
  obtain ⟨⟨C,hC,hb⟩,hl⟩ := C4k_K_2.exactness hk hv
  exact ⟨⟨C,hC.1,hC.2,hb⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
#guard_standard_axioms exactness_explicit
#print axioms exactness_explicit
end CoveringDesigns.AuditC4k_K_2


#check (@CoveringDesigns.C4k_K_2.affine_attainment :
∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  4 ≤ k → Fintype.card α = 4 * k → 4 ∣ k → ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 2 ∧ Finset.card C ≤ 20)
#guard_standard_axioms CoveringDesigns.C4k_K_2.affine_attainment
#print axioms CoveringDesigns.C4k_K_2.affine_attainment

#check (@CoveringDesigns.C4k_K_2.upper_bound :
∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  8 ≤ k → Fintype.card α = 4 * k → ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 2 ∧ Finset.card C ≤ if 4 ∣ k then 20 else 21)
#guard_standard_axioms CoveringDesigns.C4k_K_2.upper_bound
#print axioms CoveringDesigns.C4k_K_2.upper_bound

#check (@CoveringDesigns.C4k_K_2.Barker.blocks :
List (Finset (Fin 44)))
#guard_standard_axioms CoveringDesigns.C4k_K_2.Barker.blocks
#print axioms CoveringDesigns.C4k_K_2.Barker.blocks

#check (@CoveringDesigns.C4k_K_2.Barker.blocks_distinct :
CoveringDesigns.C4k_K_2.Barker.blocks.Nodup)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Barker.blocks_distinct
#print axioms CoveringDesigns.C4k_K_2.Barker.blocks_distinct

#check (@CoveringDesigns.C4k_K_2.Barker.family :
CoveringDesigns.Family (Fin 44))
#guard_standard_axioms CoveringDesigns.C4k_K_2.Barker.family
#print axioms CoveringDesigns.C4k_K_2.Barker.family

#check (@CoveringDesigns.C4k_K_2.Barker.family_card :
Finset.card CoveringDesigns.C4k_K_2.Barker.family = 21)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Barker.family_card
#print axioms CoveringDesigns.C4k_K_2.Barker.family_card

#check (@CoveringDesigns.C4k_K_2.Barker.family_uniform :
CoveringDesigns.Uniform CoveringDesigns.C4k_K_2.Barker.family 11)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Barker.family_uniform
#print axioms CoveringDesigns.C4k_K_2.Barker.family_uniform

#check (@CoveringDesigns.C4k_K_2.Barker.family_covers :
CoveringDesigns.Covers CoveringDesigns.C4k_K_2.Barker.family 2)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Barker.family_covers
#print axioms CoveringDesigns.C4k_K_2.Barker.family_covers

#check (@CoveringDesigns.C4k_K_2.Barker.family_isCover :
CoveringDesigns.IsCover CoveringDesigns.C4k_K_2.Barker.family 11 2)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Barker.family_isCover
#print axioms CoveringDesigns.C4k_K_2.Barker.family_isCover

#check (@CoveringDesigns.C4k_K_2.Barker.attainment :
∀ {α : Type u_1} [inst : Fintype α], Fintype.card α = 44 → ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 11 2 ∧ Finset.card C = 21)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Barker.attainment
#print axioms CoveringDesigns.C4k_K_2.Barker.attainment

#check (@CoveringDesigns.C4k_K_2.Examples.c32_8_2 :
(∃ C : CoveringDesigns.Family (Fin 32), CoveringDesigns.IsCover C 8 2 ∧ Finset.card C = 20) ∧
  ∀ (C : CoveringDesigns.Family (Fin 32)), CoveringDesigns.IsCover C 8 2 → 20 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Examples.c32_8_2
#print axioms CoveringDesigns.C4k_K_2.Examples.c32_8_2

#check (@CoveringDesigns.C4k_K_2.Examples.c36_9_2 :
(∃ C : CoveringDesigns.Family (Fin 36), CoveringDesigns.IsCover C 9 2 ∧ Finset.card C = 21) ∧
  ∀ (C : CoveringDesigns.Family (Fin 36)), CoveringDesigns.IsCover C 9 2 → 21 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Examples.c36_9_2
#print axioms CoveringDesigns.C4k_K_2.Examples.c36_9_2

#check (@CoveringDesigns.C4k_K_2.Examples.c40_10_2 :
(∃ C : CoveringDesigns.Family (Fin 40), CoveringDesigns.IsCover C 10 2 ∧ Finset.card C = 21) ∧
  ∀ (C : CoveringDesigns.Family (Fin 40)), CoveringDesigns.IsCover C 10 2 → 21 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Examples.c40_10_2
#print axioms CoveringDesigns.C4k_K_2.Examples.c40_10_2

#check (@CoveringDesigns.C4k_K_2.Examples.c44_11_2 :
(∃ C : CoveringDesigns.Family (Fin 44), CoveringDesigns.IsCover C 11 2 ∧ Finset.card C = 21) ∧
  ∀ (C : CoveringDesigns.Family (Fin 44)), CoveringDesigns.IsCover C 11 2 → 21 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Examples.c44_11_2
#print axioms CoveringDesigns.C4k_K_2.Examples.c44_11_2

#check (@CoveringDesigns.C4k_K_2.Examples.c60_15_2 :
(∃ C : CoveringDesigns.Family (Fin 60), CoveringDesigns.IsCover C 15 2 ∧ Finset.card C = 21) ∧
  ∀ (C : CoveringDesigns.Family (Fin 60)), CoveringDesigns.IsCover C 15 2 → 21 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C4k_K_2.Examples.c60_15_2
#print axioms CoveringDesigns.C4k_K_2.Examples.c60_15_2

#check (@CoveringDesigns.C4k_K_2.indexed_twenty :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [DecidableEq I] [inst_2 : Fintype X] [inst_3 : DecidableEq X] {k : ℕ}
  {B : I → Finset X}, 4 ≤ k → Fintype.card X = 4 * k → CoveringDesigns.Multicover.IsCover B k 2 1 → 20 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C4k_K_2.indexed_twenty
#print axioms CoveringDesigns.C4k_K_2.indexed_twenty

#check (@CoveringDesigns.C4k_K_2.indexed_twenty_one :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [DecidableEq I] [inst_2 : Fintype X] [inst_3 : DecidableEq X] {k : ℕ}
  {B : I → Finset X},
  4 ≤ k → Fintype.card X = 4 * k → CoveringDesigns.Multicover.IsCover B k 2 1 → ¬4 ∣ k → 21 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C4k_K_2.indexed_twenty_one
#print axioms CoveringDesigns.C4k_K_2.indexed_twenty_one

#check (@CoveringDesigns.C4k_K_2.lower_bound :
∀ {X : Type u_2} [inst : Fintype X] {k : ℕ} {C : CoveringDesigns.Family X},
  8 ≤ k → Fintype.card X = 4 * k → CoveringDesigns.IsCover C k 2 → (if 4 ∣ k then 20 else 21) ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C4k_K_2.lower_bound
#print axioms CoveringDesigns.C4k_K_2.lower_bound

#check (@CoveringDesigns.C4k_K_2.attainment :
∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  8 ≤ k → Fintype.card α = 4 * k → ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 2 ∧ Finset.card C = if 4 ∣ k then 20 else 21)
#guard_standard_axioms CoveringDesigns.C4k_K_2.attainment
#print axioms CoveringDesigns.C4k_K_2.attainment

#check (@CoveringDesigns.C4k_K_2.exactness :
∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  8 ≤ k →
    Fintype.card α = 4 * k →
      (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 2 ∧ Finset.card C = if 4 ∣ k then 20 else 21) ∧
        ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C k 2 → (if 4 ∣ k then 20 else 21) ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C4k_K_2.exactness
#print axioms CoveringDesigns.C4k_K_2.exactness

#check (@CoveringDesigns.C4k_K_2.covering_number :
∀ {k : ℕ},
  8 ≤ k →
    (∃ C : CoveringDesigns.Family (Fin (4*k)), CoveringDesigns.IsCover C k 2 ∧ Finset.card C = if 4 ∣ k then 20 else 21) ∧
      ∀ (C : CoveringDesigns.Family (Fin (4 * k))),
        CoveringDesigns.IsCover C k 2 → (if 4 ∣ k then 20 else 21) ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C4k_K_2.covering_number
#print axioms CoveringDesigns.C4k_K_2.covering_number
