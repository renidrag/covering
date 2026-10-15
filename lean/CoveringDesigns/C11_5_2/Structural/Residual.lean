import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-! The residual graph in Stanton's structural template is one edge together
with a complete bipartite graph on two pairs.  This module proves directly
that its two four-point covering sets have the required template form. -/

namespace CoveringDesigns.StantonStructural

open Finset

variable {α : Type*} [DecidableEq α]

/-- The pairs left uncovered by the four doubled-edge blocks. -/
def residualEdge (C D : Finset α) (s t x y : α) : Prop :=
  (x = s ∧ y = t) ∨ (x = t ∧ y = s) ∨
  (x ∈ C ∧ y ∈ D) ∨ (x ∈ D ∧ y ∈ C)

private theorem pair_eq_of_members {P : Finset α} {s t : α}
    (hP : P.card = 2) (hst : s ≠ t) (hs : s ∈ P) (ht : t ∈ P) :
    P = {s, t} := by
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · simp [hP, hst]

private theorem exists_outside_pair {P C D : Finset α} {s t : α}
    (hP : P.card = 2) (hst : s ≠ t)
    (hPX : P ⊆ {s, t} ∪ (C ∪ D)) (hne : P ≠ {s, t}) :
    ∃ x ∈ P, x ∈ C ∨ x ∈ D := by
  by_contra hn
  apply hne
  apply eq_of_subset_of_card_le
  · intro x hx
    rcases mem_union.mp (hPX hx) with hxst | hxCD
    · exact hxst
    · exact False.elim (hn ⟨x, hx, mem_union.mp hxCD⟩)
  · simp [hst, hP]

private theorem residual_pair_same_side {P Q C D : Finset α} {s t p q : α}
    (hP : P.card = 2) (hQ : Q.card = 2) (hC : C.card = 2)
    (hst : s ≠ t) (hPQ : Disjoint P Q)
    (hPX : P ⊆ {s, t} ∪ (C ∪ D)) (hQX : Q ⊆ {s, t} ∪ (C ∪ D))
    (hp : p ∈ P) (hpC : p ∈ C) (hq : q ∈ Q) (hqC : q ∈ C)
    (hcross : ∀ x ∈ P, ∀ y ∈ Q, ¬ residualEdge C D s t x y) :
    P = {s, t} ∨ Q = {s, t} := by
  have hPD : ∀ x ∈ P, x ∉ D := by
    intro x hx hxD
    exact hcross x hx q hq (Or.inr (Or.inr (Or.inr ⟨hxD, hqC⟩)))
  have hQD : ∀ y ∈ Q, y ∉ D := by
    intro y hy hyD
    exact hcross p hp y hy (Or.inr (Or.inr (Or.inl ⟨hpC, hyD⟩)))
  have hsub : P ∪ Q ⊆ {s, t} ∪ C := by
    intro x hx
    rcases mem_union.mp hx with hxP | hxQ
    · rcases mem_union.mp (hPX hxP) with hxst | hxCD
      · exact mem_union_left _ hxst
      · rcases mem_union.mp hxCD with hxC | hxD
        · exact mem_union_right _ hxC
        · exact False.elim (hPD x hxP hxD)
    · rcases mem_union.mp (hQX hxQ) with hxst | hxCD
      · exact mem_union_left _ hxst
      · rcases mem_union.mp hxCD with hxC | hxD
        · exact mem_union_right _ hxC
        · exact False.elim (hQD x hxQ hxD)
  have heq : P ∪ Q = {s, t} ∪ C := by
    apply eq_of_subset_of_card_le hsub
    calc
      ({s, t} ∪ C).card ≤ ({s, t} : Finset α).card + C.card := card_union_le _ _
      _ = (P ∪ Q).card := by simp [card_union_of_disjoint hPQ, hP, hQ, hC, hst]
  have hs : s ∈ P ∪ Q := by rw [heq]; simp
  have ht : t ∈ P ∪ Q := by rw [heq]; simp
  rcases mem_union.mp hs with hs | hs <;> rcases mem_union.mp ht with ht | ht
  · exact Or.inl (pair_eq_of_members hP hst hs ht)
  · exact False.elim (hcross s hs t ht (Or.inl ⟨rfl, rfl⟩))
  · exact False.elim (hcross t ht s hs (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact Or.inr (pair_eq_of_members hQ hst hs ht)

/-- Two disjoint pairs avoiding all residual edges between them include `{s,t}`.
The conclusion needs only the pair sizes: disjointness of the template cells
is not needed for this graph lemma. -/
theorem residual_difference_pair {P Q C D : Finset α} {s t : α}
    (hP : P.card = 2) (hQ : Q.card = 2)
    (hC : C.card = 2) (hD : D.card = 2) (hst : s ≠ t)
    (hPQ : Disjoint P Q)
    (hPX : P ⊆ {s, t} ∪ (C ∪ D)) (hQX : Q ⊆ {s, t} ∪ (C ∪ D))
    (hcross : ∀ x ∈ P, ∀ y ∈ Q, ¬ residualEdge C D s t x y) :
    P = {s, t} ∨ Q = {s, t} := by
  by_cases hPS : P = {s, t}
  · exact Or.inl hPS
  by_cases hQS : Q = {s, t}
  · exact Or.inr hQS
  obtain ⟨p, hp, hpC | hpD⟩ := exists_outside_pair hP hst hPX hPS
  · obtain ⟨q, hq, hqC | hqD⟩ := exists_outside_pair hQ hst hQX hQS
    · exact residual_pair_same_side hP hQ hC hst hPQ hPX hQX hp hpC hq hqC hcross
    · exact False.elim (hcross p hp q hq (Or.inr (Or.inr (Or.inl ⟨hpC, hqD⟩))))
  · obtain ⟨q, hq, hqC | hqD⟩ := exists_outside_pair hQ hst hQX hQS
    · exact False.elim (hcross p hp q hq (Or.inr (Or.inr (Or.inr ⟨hpD, hqC⟩))))
    · apply residual_pair_same_side hP hQ hD hst hPQ
        (by simpa [union_comm C D] using hPX)
        (by simpa [union_comm C D] using hQX) hp hpD hq hqD
      intro x hx y hy he
      apply hcross x hx y hy
      rcases he with he | he | he | he
      · exact Or.inl he
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inr he))
      · exact Or.inr (Or.inr (Or.inl he))

/-- Covering the residual edge and the four cross-pairs by two four-sets
forces one four-set to be `C ∪ D`; the other adds a pair to `{s,t}`. -/
theorem residual_completion {U V C D : Finset α} {s t : α}
    (hC : C.card = 2) (hD : D.card = 2) (hst : s ≠ t)
    (hCD : Disjoint C D) (hs : s ∉ C ∪ D) (ht : t ∉ C ∪ D)
    (hU : U.card = 4) (hV : V.card = 4)
    (hUnion : U ∪ V = {s, t} ∪ (C ∪ D))
    (hST : (s ∈ U ∧ t ∈ U) ∨ (s ∈ V ∧ t ∈ V))
    (hCross : ∀ c ∈ C, ∀ d ∈ D,
      (c ∈ U ∧ d ∈ U) ∨ (c ∈ V ∧ d ∈ V)) :
    ∃ R : Finset α, R ⊆ C ∪ D ∧ R.card = 2 ∧
      ((U = C ∪ D ∧ V = {s, t} ∪ R) ∨
       (V = C ∪ D ∧ U = {s, t} ∪ R)) := by
  have hSC : Disjoint ({s, t} : Finset α) (C ∪ D) := by
    apply disjoint_left.mpr
    intro x hx hxCD
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hs hxCD
    · exact ht hxCD
  have hCDcard : (C ∪ D).card = 4 := by
    rw [card_union_of_disjoint hCD, hC, hD]
  have hUVcard : (U ∪ V).card = 6 := by
    rw [hUnion, card_union_of_disjoint hSC, hCDcard]
    simp [hst]
  have hP : (U \ V).card = 2 := by
    have hh := card_sdiff_add_card U V
    omega
  have hQ : (V \ U).card = 2 := by
    have hh := card_sdiff_add_card V U
    rw [union_comm V U] at hh
    omega
  have hPQ : Disjoint (U \ V) (V \ U) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1
  have hPX : U \ V ⊆ {s, t} ∪ (C ∪ D) := by
    rw [← hUnion]
    exact sdiff_subset.trans subset_union_left
  have hQX : V \ U ⊆ {s, t} ∪ (C ∪ D) := by
    rw [← hUnion]
    exact sdiff_subset.trans subset_union_right
  have hcover : ∀ x y, residualEdge C D s t x y →
      (x ∈ U ∧ y ∈ U) ∨ (x ∈ V ∧ y ∈ V) := by
    intro x y he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | he | he
    · exact hST
    · exact hST.imp And.symm And.symm
    · exact hCross x he.1 y he.2
    · exact (hCross y he.2 x he.1).imp And.symm And.symm
  have hno : ∀ x ∈ U \ V, ∀ y ∈ V \ U, ¬ residualEdge C D s t x y := by
    intro x hx y hy he
    rcases hcover x y he with hh | hh
    · exact (mem_sdiff.mp hy).2 hh.2
    · exact (mem_sdiff.mp hx).2 hh.1
  have finish : ∀ A B : Finset α, A.card = 4 → B.card = 4 →
      A ∪ B = {s, t} ∪ (C ∪ D) → B \ A = {s, t} →
      ∃ R : Finset α, R ⊆ C ∪ D ∧ R.card = 2 ∧
        A = C ∪ D ∧ B = {s, t} ∪ R := by
    intro A B hA hB hAB hdiff
    have hAsub : A ⊆ C ∪ D := by
      intro x hx
      have hxAB : x ∈ {s, t} ∪ (C ∪ D) := by
        rw [← hAB]
        exact mem_union_left _ hx
      rcases mem_union.mp hxAB with hxst | hxCD
      · rw [← hdiff] at hxst
        exact False.elim ((mem_sdiff.mp hxst).2 hx)
      · exact hxCD
    have hAeq : A = C ∪ D := eq_of_subset_of_card_le hAsub (by omega)
    refine ⟨A ∩ B, inter_subset_left.trans hAeq.subset, ?_, hAeq, ?_⟩
    · have hh := card_union_add_card_inter A B
      have hABcard : (A ∪ B).card = 6 := by
        rw [hAB, card_union_of_disjoint hSC, hCDcard]
        simp [hst]
      omega
    · rw [← hdiff]
      ext x
      by_cases hx : x ∈ A <;> simp [hx]
  rcases residual_difference_pair hP hQ hC hD hst hPQ hPX hQX hno with hdiff | hdiff
  · obtain ⟨R, hR, hRc, hVeq, hUeq⟩ :=
      finish V U hV hU (by simpa [union_comm] using hUnion) hdiff
    exact ⟨R, hR, hRc, Or.inr ⟨hVeq, hUeq⟩⟩
  · obtain ⟨R, hR, hRc, hUeq, hVeq⟩ := finish U V hU hV hUnion hdiff
    exact ⟨R, hR, hRc, Or.inl ⟨hUeq, hVeq⟩⟩

end CoveringDesigns.StantonStructural
