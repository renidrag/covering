import CoveringDesigns.Foundations.PairCapacity
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

/-!
The four two-point intersections, viewed through their complementary triples.
No classification of graphs or of covering configurations is used.
-/

namespace CoveringDesigns.StantonStructural

open Finset

variable {α : Type*} [DecidableEq α]

/-- Three disjoint pairs cannot fit inside a five-element set. -/
theorem three_pairs_not_disjoint {A P Q R : Finset α}
    (hA : A.card = 5) (hP : P.card = 2) (hQ : Q.card = 2) (hR : R.card = 2)
    (hPA : P ⊆ A) (hQA : Q ⊆ A) (hRA : R ⊆ A)
    (hPQ : Disjoint P Q) (hPR : Disjoint P R) (hQR : Disjoint Q R) : False := by
  have hu : P ∪ Q ∪ R ⊆ A := union_subset (union_subset hPA hQA) hRA
  have hc := card_le_card hu
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hPR, hQR⟩),
    card_union_of_disjoint hPQ, hP, hQ, hR, hA] at hc
  omega

/-- A nonempty subset cannot equal its relative complement. -/
theorem ne_relative_complement {X T : Finset α} (hT : T.Nonempty) : T ≠ X \ T := by
  intro h
  obtain ⟨x, hx⟩ := hT
  have hx' : x ∈ X \ T := h ▸ hx
  exact (mem_sdiff.mp hx').2 hx

/-- The information about the four double-intersection blocks needed below.
`no_single` is the elementary nine-pairs-versus-eight-capacity obstruction. -/
structure FourTraceSystem (α : Type*) [DecidableEq α] where
  A : Finset α
  X : Finset α
  cardA : A.card = 5
  cardX : X.card = 6
  edge : Fin 4 → Finset α
  trace : Fin 4 → Finset α
  edge_subset : ∀ i, edge i ⊆ A
  trace_subset : ∀ i, trace i ⊆ X
  edge_card : ∀ i, (edge i).card = 2
  trace_card : ∀ i, (trace i).card = 3
  meet_complement : ∀ i j, i ≠ j → (edge i ∩ edge j).Nonempty →
    trace j = X \ trace i
  no_single : ∀ T : Finset α, T ⊆ X → T.card = 3 →
    ¬ (∀ i, trace i = T ∨ trace i = X \ T)

namespace FourTraceSystem

variable (S : FourTraceSystem α)

theorem trace_nonempty (i : Fin 4) : (S.trace i).Nonempty := by
  apply card_pos.mp
  rw [S.trace_card]
  omega

theorem disjoint_edges_of_not_complement {i j : Fin 4}
    (hij : i ≠ j) (ht : S.trace j ≠ S.X \ S.trace i) :
    Disjoint (S.edge i) (S.edge j) := by
  by_contra h
  exact ht (S.meet_complement i j hij (not_disjoint_iff_nonempty_inter.mp h))

theorem trace_injective : Function.Injective S.trace := by
  intro i j ht
  by_contra hij
  have hd : Disjoint (S.edge i) (S.edge j) :=
    S.disjoint_edges_of_not_complement hij (by
      rw [← ht]
      exact ne_relative_complement (S.trace_nonempty i))
  apply S.no_single (S.trace i) (S.trace_subset i) (S.trace_card i)
  intro k
  by_cases hki : k = i
  · exact Or.inl (hki ▸ rfl)
  by_cases hkj : k = j
  · exact Or.inl (hkj ▸ ht.symm)
  right
  by_cases hki' : (S.edge i ∩ S.edge k).Nonempty
  · exact S.meet_complement i k (Ne.symm hki) hki'
  have hdik : Disjoint (S.edge i) (S.edge k) := by
    by_contra h
    exact hki' (not_disjoint_iff_nonempty_inter.mp h)
  have hjk : (S.edge j ∩ S.edge k).Nonempty := by
    by_contra h
    have hdjk : Disjoint (S.edge j) (S.edge k) := by
      by_contra hd'
      exact h (not_disjoint_iff_nonempty_inter.mp hd')
    exact three_pairs_not_disjoint S.cardA (S.edge_card i) (S.edge_card j)
      (S.edge_card k) (S.edge_subset i) (S.edge_subset j) (S.edge_subset k)
      hd hdik hdjk
  rw [S.meet_complement j k (Ne.symm hkj) hjk, ← ht]

/-- There is a trace outside the partition determined by any chosen trace. -/
theorem exists_other_partition (i : Fin 4) :
    ∃ j, S.trace j ≠ S.trace i ∧ S.trace j ≠ S.X \ S.trace i := by
  by_contra h
  apply S.no_single (S.trace i) (S.trace_subset i) (S.trace_card i)
  intro j
  by_cases he : S.trace j = S.trace i
  · exact Or.inl he
  by_cases hc : S.trace j = S.X \ S.trace i
  · exact Or.inr hc
  exact False.elim (h ⟨j, he, hc⟩)

/-- An edge cannot be disjoint from two already disjoint pairs in `A`.
Consequently its trace complements one of their traces. -/
theorem trace_two_alternatives {i j k : Fin 4}
    (hd : Disjoint (S.edge i) (S.edge j)) (hki : k ≠ i) (hkj : k ≠ j) :
    S.trace k = S.X \ S.trace i ∨ S.trace k = S.X \ S.trace j := by
  by_cases hi : (S.edge i ∩ S.edge k).Nonempty
  · exact Or.inl (S.meet_complement i k (Ne.symm hki) hi)
  have hdik : Disjoint (S.edge i) (S.edge k) := by
    by_contra h
    exact hi (not_disjoint_iff_nonempty_inter.mp h)
  have hj : (S.edge j ∩ S.edge k).Nonempty := by
    by_contra h
    have hdjk : Disjoint (S.edge j) (S.edge k) := by
      by_contra h'
      exact h (not_disjoint_iff_nonempty_inter.mp h')
    exact three_pairs_not_disjoint S.cardA (S.edge_card i) (S.edge_card j)
      (S.edge_card k) (S.edge_subset i) (S.edge_subset j) (S.edge_subset k)
      hd hdik hdjk
  exact Or.inr (S.meet_complement j k (Ne.symm hkj) hj)

/-- Once two traces are complementary, every other edge is disjoint from
their union: an intersection would give a repeated trace. -/
theorem disjoint_of_complement_pair {i j k : Fin 4}
    (hpair : S.trace j = S.X \ S.trace i) (hik : i ≠ k) (hjk : j ≠ k) :
    Disjoint (S.edge i ∪ S.edge j) (S.edge k) := by
  apply disjoint_union_left.mpr
  constructor
  · apply S.disjoint_edges_of_not_complement hik
    intro h
    exact hjk (S.trace_injective (hpair.trans h.symm))
  · apply S.disjoint_edges_of_not_complement hjk
    intro h
    have hback : S.trace i = S.X \ S.trace j := by
      rw [hpair, Finset.sdiff_sdiff_eq_self (S.trace_subset i)]
    exact hik (S.trace_injective (hback.trans h.symm))

/-- The four traces form two complementary pairs from distinct partitions.
The unions of the corresponding edge pairs are disjoint. -/
theorem complement_pairing :
    ∃ e : Equiv.Perm (Fin 4),
      S.trace (e 1) = S.X \ S.trace (e 0) ∧
      S.trace (e 3) = S.X \ S.trace (e 2) ∧
      Disjoint (S.edge (e 0) ∪ S.edge (e 1)) (S.edge (e 2) ∪ S.edge (e 3)) := by
  classical
  obtain ⟨j, hjt, hjc⟩ := S.exists_other_partition 0
  have hj0 : j ≠ 0 := by
    intro h
    exact hjt (congrArg S.trace h)
  have hd : Disjoint (S.edge 0) (S.edge j) :=
    S.disjoint_edges_of_not_complement (Ne.symm hj0) hjc
  let remaining := ((univ : Finset (Fin 4)).erase 0).erase j
  have hjmem : j ∈ (univ : Finset (Fin 4)).erase 0 := by simp [hj0]
  have hremaining : remaining.card = 2 := by
    dsimp [remaining]
    rw [card_erase_of_mem hjmem, card_erase_of_mem (mem_univ (0 : Fin 4))]
    rfl
  obtain ⟨k, l, hkl, hremaining_eq⟩ := card_eq_two.mp hremaining
  have hk : k ∈ remaining := by rw [hremaining_eq]; simp
  have hl : l ∈ remaining := by rw [hremaining_eq]; simp
  have hkj : k ≠ j := (mem_erase.mp hk).1
  have hlj : l ≠ j := (mem_erase.mp hl).1
  have hk0 : k ≠ 0 := (mem_erase.mp (mem_erase.mp hk).2).1
  have hl0 : l ≠ 0 := (mem_erase.mp (mem_erase.mp hl).2).1
  have htk := S.trace_two_alternatives hd hk0 hkj
  have htl := S.trace_two_alternatives hd hl0 hlj
  have assemble (k l : Fin 4) (hk0 : k ≠ 0) (hl0 : l ≠ 0)
      (hkj : k ≠ j) (hlj : l ≠ j) (hkl : k ≠ l)
      (hk : S.trace k = S.X \ S.trace 0)
      (hl : S.trace l = S.X \ S.trace j) :
      ∃ e : Equiv.Perm (Fin 4),
        S.trace (e 1) = S.X \ S.trace (e 0) ∧
        S.trace (e 3) = S.X \ S.trace (e 2) ∧
        Disjoint (S.edge (e 0) ∪ S.edge (e 1)) (S.edge (e 2) ∪ S.edge (e 3)) := by
    let f : Fin 4 → Fin 4 := ![0, k, j, l]
    have hf : Function.Injective f := by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp [f, hk0, hl0, hj0, hkj, hlj, hkl] at hab ⊢ <;> omega
    let e : Equiv.Perm (Fin 4) :=
      Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
    refine ⟨e, hk, hl, ?_⟩
    change Disjoint (S.edge 0 ∪ S.edge k) (S.edge j ∪ S.edge l)
    exact disjoint_union_right.mpr
      ⟨S.disjoint_of_complement_pair hk (Ne.symm hj0) hkj,
        S.disjoint_of_complement_pair hk (Ne.symm hl0) hkl⟩
  rcases htk with htk | htk
  · have htl' : S.trace l = S.X \ S.trace j := by
      rcases htl with htl | htl
      · exact False.elim (hkl (S.trace_injective (htk.trans htl.symm)))
      · exact htl
    exact assemble k l hk0 hl0 hkj hlj hkl htk htl'
  · have htl' : S.trace l = S.X \ S.trace 0 := by
      rcases htl with htl | htl
      · exact htl
      · exact False.elim (hkl (S.trace_injective (htk.trans htl.symm)))
    exact assemble l k hl0 hk0 hlj hkj (Ne.symm hkl) htl' htk

/-- Convenient alias for the pairing data used by the doubled-edge argument. -/
theorem paired_edges :
    ∃ e : Equiv.Perm (Fin 4),
      S.trace (e 1) = S.X \ S.trace (e 0) ∧
      S.trace (e 3) = S.X \ S.trace (e 2) ∧
      Disjoint (S.edge (e 0) ∪ S.edge (e 1)) (S.edge (e 2) ∪ S.edge (e 3)) :=
  S.complement_pairing

end FourTraceSystem

#guard_standard_axioms three_pairs_not_disjoint ne_relative_complement
  FourTraceSystem.trace_injective FourTraceSystem.complement_pairing
  FourTraceSystem.paired_edges

end CoveringDesigns.StantonStructural
