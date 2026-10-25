import CoveringDesigns.SevenBlock

open Finset
open scoped BigOperators
universe u_1 u_2 u_3 u_4
set_option linter.unusedVariables false

-- Explicit contracts and transitive foundational-axiom checks.
-- Bookkeeping in C19_9_3.Internal is reached through the final theorem.

#print CoveringDesigns.SevenBlock.IndexedIsomorphic
#print CoveringDesigns.SevenBlock.TemplatePoint

#check (@CoveringDesigns.SevenBlock.classification_one : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 11 →
    CoveringDesigns.Multicover.IsCover B 5 2 1 →
      Fintype.card I = 7 →
        ∃ (tag : Bool), CoveringDesigns.SevenBlock.IndexedIsomorphic B (CoveringDesigns.SevenBlock.templateBlock 1 tag))
#guard_standard_axioms CoveringDesigns.SevenBlock.classification_one
#print axioms CoveringDesigns.SevenBlock.classification_one

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


