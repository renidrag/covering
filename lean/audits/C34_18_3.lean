import CoveringDesigns.C34_18_3

/-! Full contracts, literal-family identity and transitive foundational axioms. -/
open CoveringDesigns
universe u

#print CoveringDesigns.IsCover
#print CoveringDesigns.knownBlocks13_34_18_3
#print CoveringDesigns.knownCover13_34_18_3
#print CoveringDesigns.knownCover13_34_18_3_on

#check (@CoveringDesigns.knownBlocks13_34_18_3_distinct : knownBlocks13_34_18_3.Nodup)
#guard_standard_axioms CoveringDesigns.knownBlocks13_34_18_3_distinct
#print axioms CoveringDesigns.knownBlocks13_34_18_3_distinct

#check (@CoveringDesigns.knownCover13_34_18_3_card : knownCover13_34_18_3.card = 13)
#guard_standard_axioms CoveringDesigns.knownCover13_34_18_3_card
#print axioms CoveringDesigns.knownCover13_34_18_3_card

#check (@CoveringDesigns.knownCover13_34_18_3_uniform : Uniform knownCover13_34_18_3 18)
#guard_standard_axioms CoveringDesigns.knownCover13_34_18_3_uniform
#print axioms CoveringDesigns.knownCover13_34_18_3_uniform

#check (@CoveringDesigns.knownCover13_34_18_3_covers : Covers knownCover13_34_18_3 3)
#guard_standard_axioms CoveringDesigns.knownCover13_34_18_3_covers
#print axioms CoveringDesigns.knownCover13_34_18_3_covers

#check (@CoveringDesigns.knownCover13_34_18_3_isCover : IsCover knownCover13_34_18_3 18 3)
#guard_standard_axioms CoveringDesigns.knownCover13_34_18_3_isCover
#print axioms CoveringDesigns.knownCover13_34_18_3_isCover

#check (@CoveringDesigns.upper_bound_34_18_3 : ∃ C : Family (Fin 34), IsCover C 18 3 ∧ C.card = 13)
#guard_standard_axioms CoveringDesigns.upper_bound_34_18_3
#print axioms CoveringDesigns.upper_bound_34_18_3

#check (@CoveringDesigns.knownCover13_34_18_3_on_card : ∀ {α : Type u} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 34), (knownCover13_34_18_3_on hv).card = 13)
#guard_standard_axioms CoveringDesigns.knownCover13_34_18_3_on_card
#print axioms CoveringDesigns.knownCover13_34_18_3_on_card

#check (@CoveringDesigns.knownCover13_34_18_3_on_isCover : ∀ {α : Type u} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 34), IsCover (knownCover13_34_18_3_on hv) 18 3)
#guard_standard_axioms CoveringDesigns.knownCover13_34_18_3_on_isCover
#print axioms CoveringDesigns.knownCover13_34_18_3_on_isCover

#check (@CoveringDesigns.upper_bound_34_18_3_on : ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α = 34 →
    ∃ C : Family α, IsCover C 18 3 ∧ C.card = 13)
#guard_standard_axioms CoveringDesigns.upper_bound_34_18_3_on
#print axioms CoveringDesigns.upper_bound_34_18_3_on

#check (@CoveringDesigns.lower_bound_34_18_3 : ∀ {α : Type u} [Fintype α] {C : Family α}, Fintype.card α = 34 → IsCover C 18 3 → 13 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_34_18_3
#print axioms CoveringDesigns.lower_bound_34_18_3

#check (@CoveringDesigns.covering_number_34_18_3_on : ∀ {α : Type u} [Fintype α], Fintype.card α = 34 →
    (∃ C : Family α, IsCover C 18 3 ∧ C.card = 13) ∧
    (∀ C : Family α, IsCover C 18 3 → 13 ≤ C.card))
#guard_standard_axioms CoveringDesigns.covering_number_34_18_3_on
#print axioms CoveringDesigns.covering_number_34_18_3_on

#check (@CoveringDesigns.covering_number_34_18_3 : (∃ C : Family (Fin 34), IsCover C 18 3 ∧ C.card = 13) ∧
    (∀ C : Family (Fin 34), IsCover C 18 3 → 13 ≤ C.card))
#guard_standard_axioms CoveringDesigns.covering_number_34_18_3
#print axioms CoveringDesigns.covering_number_34_18_3

namespace CoveringDesigns.Audit34_18_3

theorem covering_number_explicit {α : Type u} [Fintype α]
    (hv : Fintype.card α = 34) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 18) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 13) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 18) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 13 ≤ C.card) := by
  obtain ⟨⟨C, hC, hcard⟩, hlower⟩ := covering_number_34_18_3_on hv
  exact ⟨⟨C, hC.1, hC.2, hcard⟩, fun C hu hc => hlower C ⟨hu, hc⟩⟩

end CoveringDesigns.Audit34_18_3

#guard_standard_axioms CoveringDesigns.Audit34_18_3.covering_number_explicit
#print axioms CoveringDesigns.Audit34_18_3.covering_number_explicit
