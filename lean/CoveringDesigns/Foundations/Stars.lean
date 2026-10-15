import CoveringDesigns.Foundations.Basic

/-!
The star-compatibility reduction, before any finite catalogue is supplied.
In particular, no symmetry restriction is used here.
-/

namespace CoveringDesigns

open Finset

variable {α : Type*} [DecidableEq α]

def outside (C : Family α) (p : α) : Family α := C.filter (p ∉ ·)

def outsideStar (C : Family α) (p q : α) : Family α :=
  (outside C p).filter (q ∈ ·)

theorem outside_card_add_degree (C : Family α) (p : α) :
    (outside C p).card + degree C p = C.card := by
  simpa [outside, degree, star, Nat.add_comm] using
    card_filter_add_card_filter_not (s := C) (p := fun B => p ∈ B)

def Agree (q : α) (D : Family α) (r : α) (E : Family α) : Prop :=
  D.filter (r ∈ ·) = E.filter (q ∈ ·)

theorem actual_stars_agree (C : Family α) (p q r : α) :
    Agree q (outsideStar C p q) r (outsideStar C p r) := by
  unfold Agree outsideStar
  ext B
  simp [and_comm, and_left_comm]

theorem actual_stars_union_subset (C : Family α) (p : α) (Q : Finset α) :
    Q.biUnion (outsideStar C p) ⊆ outside C p := by
  intro B hB
  obtain ⟨q, _, hq⟩ := mem_biUnion.mp hB
  exact (mem_filter.mp hq).1

theorem actual_stars_union_card_le (C : Family α) (p : α) (Q : Finset α) :
    (Q.biUnion (outsideStar C p)).card ≤ (outside C p).card :=
  card_le_card (actual_stars_union_subset C p Q)

theorem four_other_minimum_points [Fintype α] {C : Family α} {p : α} {m : ℕ}
    (hc : 5 ≤ (minimumPoints C m).card) (hp : degree C p = m) :
    ∃ Q : Finset α, Q.card = 4 ∧ p ∉ Q ∧ ∀ q ∈ Q, degree C q = m := by
  have hpm : p ∈ minimumPoints C m := by simp [minimumPoints, hp]
  have he : 4 ≤ ((minimumPoints C m).erase p).card := by
    rw [card_erase_of_mem hpm]
    omega
  obtain ⟨Q, hQ, hcard⟩ := exists_subset_card_eq he
  refine ⟨Q, hcard, ?_, ?_⟩
  · intro h
    exact (notMem_erase p _) (hQ h)
  · intro q hq
    exact (mem_filter.mp (mem_of_mem_erase (hQ hq))).2

end CoveringDesigns
