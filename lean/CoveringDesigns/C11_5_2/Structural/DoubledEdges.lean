import CoveringDesigns.C11_5_2.Structural.Frame
import CoveringDesigns.Foundations.PartitionObstruction
import Mathlib.Algebra.BigOperators.Fin

/-! Complementary pairs of traces force two doubled edges and a common singleton.
The only obstruction is the elementary impossibility of covering a two-by-two
set of cross pairs by two disjoint triples. -/

namespace CoveringDesigns.StantonStructural

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The graph-and-trace structure forced by a six-block frame. -/
structure DoubledFrame (S : SixBlockFrame α) where
  order : Equiv.Perm (Fin 4)
  edge01 : S.edge (order 1) = S.edge (order 0)
  edge23 : S.edge (order 3) = S.edge (order 2)
  trace01 : S.trace (order 1) = S.X \ S.trace (order 0)
  trace23 : S.trace (order 3) = S.X \ S.trace (order 2)
  edges_disjoint : Disjoint (S.edge (order 0)) (S.edge (order 2))
  same_singleton : S.a = S.b
  left_eq : S.A = {S.a} ∪ S.edge (order 0) ∪ S.edge (order 2)
  right_union : S.U ∪ S.V = S.X
  left_disjoint : List.Pairwise Disjoint [{S.a}, S.edge (order 0), S.edge (order 2)]

private theorem card_filter_four (p : Fin 4 → Prop) [DecidablePred p]
    (e : Equiv.Perm (Fin 4)) :
    (univ.filter p).card =
      (if p (e 0) then 1 else 0) + (if p (e 1) then 1 else 0) +
      (if p (e 2) then 1 else 0) + (if p (e 3) then 1 else 0) := by
  rw [card_eq_sum_ones, sum_filter]
  rw [← Equiv.sum_comp e (fun i => if p i then (1 : ℕ) else 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero, Nat.add_assoc]
  rfl

namespace SixBlockFrame

variable (S : SixBlockFrame α)

/-- Complementary trace pairs use every point twice, so the singleton traces
must together supply the remaining required incidence at every right point. -/
theorem right_union_of_trace_pairing (e : Equiv.Perm (Fin 4))
    (h01 : S.trace (e 1) = S.X \ S.trace (e 0))
    (h23 : S.trace (e 3) = S.X \ S.trace (e 2)) : S.U ∪ S.V = S.X := by
  apply subset_antisymm (union_subset S.U_subset S.V_subset)
  intro x hx
  have hc : (univ.filter fun i => x ∈ S.trace i).card = 2 := by
    rw [card_filter_four _ e, h01, h23]
    by_cases h0 : x ∈ S.trace (e 0) <;> by_cases h2 : x ∈ S.trace (e 2) <;>
      simp [hx, h0, h2]
  by_cases hu : x ∈ S.U
  · exact mem_union_left _ hu
  by_cases hv : x ∈ S.V
  · exact mem_union_right _ hv
  have hd := S.right_degree x hx
  simp [hc, hu, hv] at hd

/-- A vertex on exactly one edge is a singleton vertex. Its lone edge must
cover every right point omitted by that singleton's four-point trace. -/
private theorem unique_edge_data (i : Fin 4) (x : α) (hx : x ∈ S.A)
    (hu : ∀ j, x ∈ S.edge j ↔ j = i) :
    (x = S.a ∧ x ≠ S.b ∧ S.V \ S.U ⊆ S.trace i) ∨
      (x = S.b ∧ x ≠ S.a ∧ S.U \ S.V ⊆ S.trace i) := by
  have hf : (univ.filter fun j => x ∈ S.edge j) = {i} := by
    ext j
    simp [hu j]
  have hd := S.edge_degree x hx
  rw [hf, card_singleton] at hd
  by_cases ha : x = S.a
  · have hb : x ≠ S.b := by
      intro hb
      have hab : S.a = S.b := ha.symm.trans hb
      simp [ha, hab] at hd
    left
    refine ⟨ha, hb, ?_⟩
    intro y hy
    rcases S.left_cover x hx y (S.V_subset (mem_sdiff.mp hy).1) with
      ⟨j, hxj, hyj⟩ | hyU | hyV
    · simpa [(hu j).mp hxj] using hyj
    · exact False.elim ((mem_sdiff.mp hy).2 hyU.2)
    · exact False.elim (hb hyV.1)
  · have hb : x = S.b := by
      by_contra hn
      simp [ha, hn] at hd
    right
    refine ⟨hb, ha, ?_⟩
    intro y hy
    rcases S.left_cover x hx y (S.U_subset (mem_sdiff.mp hy).1) with
      ⟨j, hxj, hyj⟩ | hyU | hyV
    · simpa [(hu j).mp hxj] using hyj
    · exact False.elim (ha hyU.1)
    · exact False.elim ((mem_sdiff.mp hy).2 hyV.2)

private theorem differences_not_separated (e : Equiv.Perm (Fin 4))
    (h01 : S.trace (e 1) = S.X \ S.trace (e 0))
    (h23 : S.trace (e 3) = S.X \ S.trace (e 2))
    (hsep :
      (S.U \ S.V ⊆ S.trace (e 0) ∧ S.V \ S.U ⊆ S.trace (e 1)) ∨
      (S.U \ S.V ⊆ S.trace (e 1) ∧ S.V \ S.U ⊆ S.trace (e 0))) : False := by
  have hu := S.right_union_of_trace_pairing e h01 h23
  have hP : (S.U \ S.V).card = 2 := by
    have hc := card_sdiff_add_card S.U S.V
    rw [S.V_card, hu, S.cardX] at hc
    omega
  have hQ : (S.V \ S.U).card = 2 := by
    have hc := card_sdiff_add_card S.V S.U
    rw [S.U_card, union_comm S.V S.U, hu, S.cardX] at hc
    omega
  have hPQ : Disjoint (S.U \ S.V) (S.V \ S.U) :=
    disjoint_left.mpr fun _ hp hq => (mem_sdiff.mp hp).2 (mem_sdiff.mp hq).1
  have hd01 : Disjoint (S.trace (e 0)) (S.trace (e 1)) := by
    rw [h01]
    exact disjoint_sdiff_self_right
  have hd23 : Disjoint (S.trace (e 2)) (S.trace (e 3)) := by
    rw [h23]
    exact disjoint_sdiff_self_right
  apply two_disjoint_triples_not_cover_two_by_two
    (S.U \ S.V) (S.V \ S.U) (S.trace (e 2)) (S.trace (e 3))
    hPQ hP hQ hd23 (by rw [S.trace_card]) (by rw [S.trace_card])
  intro p hp q hq
  have hpX := S.U_subset (mem_sdiff.mp hp).1
  have hqX := S.V_subset (mem_sdiff.mp hq).1
  have hpq : p ≠ q := by
    rintro rfl
    exact (mem_sdiff.mp hp).2 (mem_sdiff.mp hq).1
  have hn0 : ¬ (p ∈ S.trace (e 0) ∧ q ∈ S.trace (e 0)) := by
    intro hm
    rcases hsep with hsep | hsep
    · exact disjoint_left.mp hd01 hm.2 (hsep.2 hq)
    · exact disjoint_left.mp hd01 hm.1 (hsep.1 hp)
  have hn1 : ¬ (p ∈ S.trace (e 1) ∧ q ∈ S.trace (e 1)) := by
    intro hm
    rcases hsep with hsep | hsep
    · exact disjoint_left.mp hd01 (hsep.1 hp) hm.1
    · exact disjoint_left.mp hd01 (hsep.2 hq) hm.2
  rcases S.right_cover p hpX q hqX hpq with ⟨i, hpi, hqi⟩ | hm | hm
  · obtain ⟨j, rfl⟩ := e.surjective i
    fin_cases j
    · exact False.elim (hn0 ⟨hpi, hqi⟩)
    · exact False.elim (hn1 ⟨hpi, hqi⟩)
    · exact Or.inl ⟨hpi, hqi⟩
    · exact Or.inr ⟨hpi, hqi⟩
  · exact False.elim ((mem_sdiff.mp hq).2 hm.2)
  · exact False.elim ((mem_sdiff.mp hp).2 hm.1)

/-- Unequal paired edges have exclusive vertices. Each would have to be a
different singleton vertex, separating the two difference pairs into the
complementary traces. The other trace pair cannot cover their cross pairs. -/
private theorem edge_pair_equal (e : Equiv.Perm (Fin 4))
    (h01 : S.trace (e 1) = S.X \ S.trace (e 0))
    (h23 : S.trace (e 3) = S.X \ S.trace (e 2))
    (hd : Disjoint (S.edge (e 0) ∪ S.edge (e 1))
      (S.edge (e 2) ∪ S.edge (e 3))) : S.edge (e 1) = S.edge (e 0) := by
  by_contra hne
  have hn01 : ¬ S.edge (e 0) ⊆ S.edge (e 1) := by
    intro hs
    exact hne (eq_of_subset_of_card_le hs (by rw [S.edge_card, S.edge_card])).symm
  have hn10 : ¬ S.edge (e 1) ⊆ S.edge (e 0) := by
    intro hs
    exact hne (eq_of_subset_of_card_le hs (by rw [S.edge_card, S.edge_card]))
  obtain ⟨x, hx0, hx1⟩ := not_subset.mp hn01
  obtain ⟨y, hy1, hy0⟩ := not_subset.mp hn10
  have hxy : x ≠ y := by
    rintro rfl
    exact hx1 hy1
  have hxu : ∀ j, x ∈ S.edge j ↔ j = e 0 := by
    intro j
    constructor
    · intro hxj
      obtain ⟨k, rfl⟩ := e.surjective j
      fin_cases k
      · rfl
      · exact False.elim (hx1 hxj)
      · exact False.elim (disjoint_left.mp hd (mem_union_left _ hx0)
          (mem_union_left _ hxj))
      · exact False.elim (disjoint_left.mp hd (mem_union_left _ hx0)
          (mem_union_right _ hxj))
    · rintro rfl
      exact hx0
  have hyu : ∀ j, y ∈ S.edge j ↔ j = e 1 := by
    intro j
    constructor
    · intro hyj
      obtain ⟨k, rfl⟩ := e.surjective j
      fin_cases k
      · exact False.elim (hy0 hyj)
      · rfl
      · exact False.elim (disjoint_left.mp hd (mem_union_right _ hy1)
          (mem_union_left _ hyj))
      · exact False.elim (disjoint_left.mp hd (mem_union_right _ hy1)
          (mem_union_right _ hyj))
    · rintro rfl
      exact hy1
  have hx := S.unique_edge_data (e 0) x (S.edge_subset _ hx0) hxu
  have hy := S.unique_edge_data (e 1) y (S.edge_subset _ hy1) hyu
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hxy (hx.1.trans hy.1.symm)
  · exact S.differences_not_separated e h01 h23 (Or.inr ⟨hy.2.2, hx.2.2⟩)
  · exact S.differences_not_separated e h01 h23 (Or.inl ⟨hx.2.2, hy.2.2⟩)
  · exact hxy (hx.1.trans hy.1.symm)

/-- Any complementary pairing supplied by the trace argument has doubled
edges and a common singleton. -/
def doubled_of_pairing (e : Equiv.Perm (Fin 4))
    (h01 : S.trace (e 1) = S.X \ S.trace (e 0))
    (h23 : S.trace (e 3) = S.X \ S.trace (e 2))
    (hd : Disjoint (S.edge (e 0) ∪ S.edge (e 1))
      (S.edge (e 2) ∪ S.edge (e 3))) : DoubledFrame S := by
  have he01 := S.edge_pair_equal e h01 h23 hd
  let e' := ((Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap 1 3)).trans e
  have he0 : e' 0 = e 2 := by simp [e', Equiv.swap_apply_def]
  have he1 : e' 1 = e 3 := by simp [e', Equiv.swap_apply_def]
  have he2 : e' 2 = e 0 := by simp [e', Equiv.swap_apply_def]
  have he3 : e' 3 = e 1 := by simp [e', Equiv.swap_apply_def]
  have he23 : S.edge (e 3) = S.edge (e 2) := by
    have hh := S.edge_pair_equal e'
      (by simpa only [he1, he0] using h23)
      (by simpa only [he3, he2] using h01)
      (by simpa only [he0, he1, he2, he3] using hd.symm)
    simpa only [he1, he0] using hh
  have hd' : Disjoint (S.edge (e 0)) (S.edge (e 2)) :=
    hd.mono subset_union_left subset_union_left
  have haDeg := S.edge_degree S.a S.a_mem
  rw [card_filter_four _ e, he01, he23] at haDeg
  have ha0 : S.a ∉ S.edge (e 0) := by
    intro hm
    simp only [hm, ite_true] at haDeg
    split_ifs at haDeg <;> omega
  have ha2 : S.a ∉ S.edge (e 2) := by
    intro hm
    simp only [hm, ite_true] at haDeg
    split_ifs at haDeg <;> omega
  have hab : S.a = S.b := by
    by_contra hne
    simp [ha0, ha2, hne] at haDeg
  have hleft : S.A = {S.a} ∪ S.edge (e 0) ∪ S.edge (e 2) := by
    apply subset_antisymm
    · intro x hx
      by_contra hn
      have hxa : x ≠ S.a := by
        intro he
        apply hn
        simp [he]
      have hx0 : x ∉ S.edge (e 0) := by
        intro hm
        exact hn (mem_union_left _ (mem_union_right _ hm))
      have hx2 : x ∉ S.edge (e 2) := by
        intro hm
        exact hn (mem_union_right _ hm)
      have hxDeg := S.edge_degree x hx
      rw [card_filter_four _ e, he01, he23] at hxDeg
      simp [hx0, hx2, hxa, ← hab] at hxDeg
    · exact union_subset (union_subset (singleton_subset_iff.mpr S.a_mem)
        (S.edge_subset _)) (S.edge_subset _)
  have hleftDisjoint : List.Pairwise Disjoint
      [{S.a}, S.edge (e 0), S.edge (e 2)] := by
    simp [List.pairwise_cons, ha0, ha2, hd']
  exact ⟨e, he01, he23, h01, h23, hd', hab, hleft,
    S.right_union_of_trace_pairing e h01 h23, hleftDisjoint⟩

/-- Every six-block frame has two doubled edges and a common singleton. -/
theorem exists_doubled_frame : Nonempty (DoubledFrame S) := by
  obtain ⟨e, h01, h23, hd⟩ := S.toFourTraceSystem.complement_pairing
  exact ⟨S.doubled_of_pairing e h01 h23 hd⟩

#guard_standard_axioms right_union_of_trace_pairing exists_doubled_frame

#print axioms exists_doubled_frame

end SixBlockFrame

end CoveringDesigns.StantonStructural
