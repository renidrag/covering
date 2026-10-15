import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
If all pairs crossing two nonempty sets are covered by two disjoint parts,
the two sets lie together in one part. This is the elementary connectedness
argument for a complete bipartite graph, expressed directly in finite sets.
-/

namespace CoveringDesigns

open Finset

variable {α : Type*} [DecidableEq α]

/-- Coverage of every cross pair by two disjoint parts forces both nonempty
sides into one of those parts. -/
theorem cross_pair_cover_forces_one_part (P Q W Z : Finset α)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hWZ : Disjoint W Z)
    (hcover : ∀ p ∈ P, ∀ q ∈ Q,
      (p ∈ W ∧ q ∈ W) ∨ (p ∈ Z ∧ q ∈ Z)) :
    P ∪ Q ⊆ W ∨ P ∪ Q ⊆ Z := by
  obtain ⟨p₀, hp₀⟩ := hP
  obtain ⟨q₀, hq₀⟩ := hQ
  have hdis := disjoint_left.mp hWZ
  rcases hcover p₀ hp₀ q₀ hq₀ with hW | hZ
  · left
    apply union_subset
    · intro p hp
      rcases hcover p hp q₀ hq₀ with hpW | hpZ
      · exact hpW.1
      · exact (hdis hW.2 hpZ.2).elim
    · intro q hq
      rcases hcover p₀ hp₀ q hq with hqW | hqZ
      · exact hqW.2
      · exact (hdis hW.1 hqZ.1).elim
  · right
    apply union_subset
    · intro p hp
      rcases hcover p hp q₀ hq₀ with hpW | hpZ
      · exact (hdis hpW.2 hZ.2).elim
      · exact hpZ.1
    · intro q hq
      rcases hcover p₀ hp₀ q hq with hqW | hqZ
      · exact (hdis hqW.1 hZ.1).elim
      · exact hqZ.2

/-- Two disjoint sets of at most three points cannot cover all cross pairs
between two disjoint two-point sets: all four points would lie in one part. -/
theorem two_disjoint_triples_not_cover_two_by_two (P Q W Z : Finset α)
    (hPQ : Disjoint P Q) (hP : P.card = 2) (hQ : Q.card = 2)
    (hWZ : Disjoint W Z) (hW : W.card ≤ 3) (hZ : Z.card ≤ 3) :
    ¬ (∀ p ∈ P, ∀ q ∈ Q,
      (p ∈ W ∧ q ∈ W) ∨ (p ∈ Z ∧ q ∈ Z)) := by
  intro hcover
  have hp : P.Nonempty := card_pos.mp (by omega)
  have hq : Q.Nonempty := card_pos.mp (by omega)
  have hfour : (P ∪ Q).card = 4 := by
    rw [card_union_of_disjoint hPQ, hP, hQ]
  rcases cross_pair_cover_forces_one_part P Q W Z hp hq hWZ hcover with hw | hz
  · have hc := card_le_card hw
    omega
  · have hc := card_le_card hz
    omega

#guard_standard_axioms cross_pair_cover_forces_one_part
  two_disjoint_triples_not_cover_two_by_two

#print axioms two_disjoint_triples_not_cover_two_by_two

end CoveringDesigns
