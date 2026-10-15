import CoveringDesigns.C11_5_2.Structural.TracePairs
import CoveringDesigns.C11_5_2.Structural.Intersections
import CoveringDesigns.C11_5_2.Structural.Degrees

/-!
The six blocks outside a block all of whose points have degree three.
Four meet that block in pairs and two meet it in single points.
-/

namespace CoveringDesigns.StantonStructural

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Incidence and pair coverage, after separating an all-low block from its
six-point complement. The four double-intersection blocks are indexed. -/
structure SixBlockFrame (α : Type*) [Fintype α] [DecidableEq α]
    extends FourTraceSystem α where
  disjointAX : Disjoint A X
  spans : A ∪ X = univ
  a : α
  b : α
  a_mem : a ∈ A
  b_mem : b ∈ A
  U : Finset α
  V : Finset α
  U_subset : U ⊆ X
  V_subset : V ⊆ X
  U_card : U.card = 4
  V_card : V.card = 4
  edge_degree : ∀ x ∈ A,
    (univ.filter fun i => x ∈ edge i).card +
      (if x = a then 1 else 0) + (if x = b then 1 else 0) = 2
  right_degree : ∀ x ∈ X,
    3 ≤ (univ.filter fun i => x ∈ trace i).card +
      (if x ∈ U then 1 else 0) + (if x ∈ V then 1 else 0)
  left_cover : ∀ x ∈ A, ∀ y ∈ X,
    (∃ i, x ∈ edge i ∧ y ∈ trace i) ∨
      (x = a ∧ y ∈ U) ∨ (x = b ∧ y ∈ V)
  right_cover : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
    (∃ i, x ∈ trace i ∧ y ∈ trace i) ∨
      (x ∈ U ∧ y ∈ U) ∨ (x ∈ V ∧ y ∈ V)

namespace SixBlockFrame

variable (S : SixBlockFrame α)

def family : Family α :=
  insert S.A ((univ.image fun i => S.edge i ∪ S.trace i) ∪
    {insert S.a S.U, insert S.b S.V})

theorem mem_family (B : Finset α) :
    B ∈ S.family ↔ B = S.A ∨ (∃ i, B = S.edge i ∪ S.trace i) ∨
      B = insert S.a S.U ∨ B = insert S.b S.V := by
  simp [family, eq_comm]
  tauto

theorem not_mem_X_of_mem_A {x : α} (hx : x ∈ S.A) : x ∉ S.X :=
  disjoint_left.mp S.disjointAX hx

theorem not_mem_A_of_mem_X {x : α} (hx : x ∈ S.X) : x ∉ S.A :=
  fun h => S.not_mem_X_of_mem_A h hx

theorem family_uniform : Uniform S.family 5 := by
  intro B hB
  rcases (S.mem_family B).mp hB with rfl | ⟨i, rfl⟩ | rfl | rfl
  · exact S.cardA
  · rw [card_union_of_disjoint (S.disjointAX.mono (S.edge_subset i) (S.trace_subset i)),
      S.edge_card, S.trace_card]
  · rw [card_insert_of_notMem (fun h => S.not_mem_X_of_mem_A S.a_mem (S.U_subset h)),
      S.U_card]
  · rw [card_insert_of_notMem (fun h => S.not_mem_X_of_mem_A S.b_mem (S.V_subset h)),
      S.V_card]

end SixBlockFrame

omit [Fintype α] in
/-- If the four triples were just one complementary pair, all nine cross pairs
would have to fit in the two four-point traces, which have capacity eight. -/
theorem no_single_trace_of_right_cover {X U V : Finset α}
    {trace : Fin 4 → Finset α}
    (hX : X.card = 6) (hU : U.card = 4) (hV : V.card = 4)
    (hcover : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      (∃ i, x ∈ trace i ∧ y ∈ trace i) ∨
        (x ∈ U ∧ y ∈ U) ∨ (x ∈ V ∧ y ∈ V))
    (T : Finset α) (hT : T ⊆ X) (hc : T.card = 3) :
    ¬ (∀ i, trace i = T ∨ trace i = X \ T) := by
  intro hsingle
  have hW : (X \ T).card = 3 := by
    rw [card_sdiff_of_subset hT, hX, hc]
  apply two_four_sets_not_cover_three_by_three T (X \ T) U V
    disjoint_sdiff_self_right hc hW (by omega) (by omega)
  intro x hx y hy
  have hne : x ≠ y := by
    intro he
    subst y
    exact (mem_sdiff.mp hy).2 hx
  rcases hcover x (hT hx) y (mem_sdiff.mp hy).1 hne with ⟨i, hxi, hyi⟩ | hu | hv
  · rcases hsingle i with he | he
    · exact False.elim ((mem_sdiff.mp hy).2 (he ▸ hyi))
    · exact False.elim ((mem_sdiff.mp (he ▸ hxi)).2 hx)
  · exact Or.inl hu
  · exact Or.inr hv

#guard_standard_axioms SixBlockFrame.family_uniform no_single_trace_of_right_cover

/- The indexing below has no mathematical symmetry assumption: it simply
chooses names for the four blocks counted by the intersection theorem. -/
private structure IndexedSixBlocks (C : Family α) (A : Finset α) where
  double : Fin 4 → Finset α
  P : Finset α
  Q : Finset α
  injective : Function.Injective double
  double_meet : ∀ i, (A ∩ double i).card = 2
  P_meet : (A ∩ P).card = 1
  Q_meet : (A ∩ Q).card = 1
  P_ne_Q : P ≠ Q
  partition : C = insert A (insert P (insert Q (univ.image double)))

private theorem indexed_six_blocks {C : Family α} {A : Finset α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    (hA : A ∈ C) (hlow : ∀ x ∈ A, degree C x = 3) :
    Nonempty (IndexedSixBlocks C A) := by
  let D := (C.erase A).filter fun B => (A ∩ B).card = 2
  let T := (C.erase A).filter fun B => (A ∩ B).card = 1
  obtain ⟨hD, hT⟩ := structural_low_block_intersection_counts hn h hC hA hlow
  change D.card = 4 at hD
  change T.card = 2 at hT
  let e : D ≃ Fin 4 := Finset.equivFinOfCardEq hD
  let B : Fin 4 → Finset α := fun i => (e.symm i).val
  have hBi : Function.Injective B := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hBD : univ.image B = D := by
    ext E
    constructor
    · rintro hm
      obtain ⟨i, _, rfl⟩ := mem_image.mp hm
      exact (e.symm i).property
    · intro hm
      exact mem_image.mpr ⟨e ⟨E, hm⟩, mem_univ _, by simp [B]⟩
  obtain ⟨P, Q, hPQ, hTQ⟩ := card_eq_two.mp hT
  have hP : P ∈ T := by rw [hTQ]; simp
  have hQ : Q ∈ T := by rw [hTQ]; simp
  have hpart : C = insert A (D ∪ T) := by
    ext E
    simp only [mem_insert, mem_union]
    constructor
    · intro hE
      by_cases hEA : E = A
      · exact Or.inl hEA
      · have hpos := (structural_blocks_intersect hn h hC hA hE (Ne.symm hEA)).card_pos
        have hup := structural_low_block_intersection_le_two hn h hC hA hE (Ne.symm hEA) hlow
        have her : E ∈ C.erase A := mem_erase.mpr ⟨hEA, hE⟩
        by_cases he : (A ∩ E).card = 2
        · exact Or.inr (Or.inl (mem_filter.mpr ⟨her, he⟩))
        · exact Or.inr (Or.inr (mem_filter.mpr ⟨her, by omega⟩))
    · rintro (rfl | hE | hE)
      · exact hA
      · exact mem_of_mem_erase (mem_filter.mp hE).1
      · exact mem_of_mem_erase (mem_filter.mp hE).1
  refine ⟨⟨B, P, Q, hBi, ?_, (mem_filter.mp hP).2, (mem_filter.mp hQ).2, hPQ, ?_⟩⟩
  · intro i
    exact (mem_filter.mp (e.symm i).property).2
  · rw [hpart, ← hBD, hTQ]
    ext E
    simp only [mem_insert, mem_union, mem_singleton]
    tauto

omit [Fintype α] in
private theorem degree_insert {C : Family α} {A : Finset α} (hA : A ∉ C) (x : α) :
    degree (insert A C) x = (if x ∈ A then 1 else 0) + degree C x := by
  by_cases hx : x ∈ A
  · simp [degree, star, filter_insert, hx, hA, Nat.add_comm]
  · simp [degree, star, filter_insert, hx]

omit [Fintype α] in
private theorem degree_image {B : Fin 4 → Finset α} (hinj : Function.Injective B) (x : α) :
    degree (univ.image B) x = (univ.filter fun i => x ∈ B i).card := by
  simp only [degree, star, filter_image]
  exact card_image_of_injective _ hinj

namespace IndexedSixBlocks

variable {C : Family α} {A : Finset α} (S : IndexedSixBlocks C A)

omit [Fintype α] in
private theorem mem_iff (E : Finset α) :
    E ∈ C ↔ E = A ∨ E = S.P ∨ E = S.Q ∨ ∃ i, E = S.double i := by
  conv_lhs => rw [S.partition]
  simp [eq_comm]

omit [Fintype α] in
private theorem double_mem (i : Fin 4) : S.double i ∈ C := by
  exact (S.mem_iff _).mpr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))

omit [Fintype α] in
private theorem P_mem : S.P ∈ C := by
  exact (S.mem_iff _).mpr (Or.inr (Or.inl rfl))

omit [Fintype α] in
private theorem Q_mem : S.Q ∈ C := by
  exact (S.mem_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))

omit [Fintype α] in
private theorem A_ne_double (hA : A.card = 5) (i : Fin 4) : A ≠ S.double i := by
  intro he
  have hm := S.double_meet i
  rw [← he, inter_self, hA] at hm
  omega

omit [Fintype α] in
private theorem A_ne_P (hA : A.card = 5) : A ≠ S.P := by
  intro he
  have hm := S.P_meet
  rw [← he, inter_self, hA] at hm
  omega

omit [Fintype α] in
private theorem A_ne_Q (hA : A.card = 5) : A ≠ S.Q := by
  intro he
  have hm := S.Q_meet
  rw [← he, inter_self, hA] at hm
  omega

omit [Fintype α] in
private theorem P_ne_double (i : Fin 4) : S.P ≠ S.double i := by
  intro he
  have hp := S.P_meet
  rw [he, S.double_meet] at hp
  omega

omit [Fintype α] in
private theorem Q_ne_double (i : Fin 4) : S.Q ≠ S.double i := by
  intro he
  have hq := S.Q_meet
  rw [he, S.double_meet] at hq
  omega

omit [Fintype α] in
private theorem degree_split (hA : A.card = 5) (x : α) :
    degree C x = (if x ∈ A then 1 else 0) +
      (if x ∈ S.P then 1 else 0) + (if x ∈ S.Q then 1 else 0) +
      (univ.filter fun i => x ∈ S.double i).card := by
  have hAm : A ∉ insert S.P (insert S.Q (univ.image S.double)) := by
    simp only [mem_insert, mem_image, mem_univ, true_and, not_or, not_exists]
    exact ⟨S.A_ne_P hA, S.A_ne_Q hA, fun i he => S.A_ne_double hA i he.symm⟩
  have hPm : S.P ∉ insert S.Q (univ.image S.double) := by
    simp only [mem_insert, mem_image, mem_univ, true_and, not_or, not_exists]
    exact ⟨S.P_ne_Q, fun i he => S.P_ne_double i he.symm⟩
  have hQm : S.Q ∉ univ.image S.double := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    exact fun i he => S.Q_ne_double i he.symm
  conv_lhs => rw [S.partition]
  rw [degree_insert hAm, degree_insert hPm, degree_insert hQm,
    degree_image S.injective]
  omega

end IndexedSixBlocks

omit [Fintype α] in
private theorem split_block (A B : Finset α) : (A ∩ B) ∪ (B \ A) = B := by
  rw [union_comm, inter_comm]
  exact sdiff_union_inter B A

omit [Fintype α] in
private theorem split_singleton {A B : Finset α} {a : α} (ha : A ∩ B = {a}) :
    B = insert a (B \ A) := by
  have hs := split_block A B
  rw [ha, singleton_union] at hs
  exact hs.symm

/-- Every all-low block in a seven-block covering yields a six-block frame.
The indexing of its four double-intersection blocks is unrestricted. -/
theorem six_block_frame_of_low_block {C : Family α} {A : Finset α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    (hA : A ∈ C) (hlow : ∀ x ∈ A, degree C x = 3) :
    ∃ S : SixBlockFrame α, S.A = A ∧ S.family = C := by
  obtain ⟨R⟩ := indexed_six_blocks hn h hC hA hlow
  obtain ⟨a, ha⟩ := card_eq_one.mp R.P_meet
  obtain ⟨b, hb⟩ := card_eq_one.mp R.Q_meet
  let X : Finset α := univ \ A
  let edge : Fin 4 → Finset α := fun i => A ∩ R.double i
  let trace : Fin 4 → Finset α := fun i => R.double i \ A
  let U : Finset α := R.P \ A
  let V : Finset α := R.Q \ A
  have hAc : A.card = 5 := h.1 A hA
  have hXc : X.card = 6 := by
    dsimp [X]
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn, hAc]
  have haA : a ∈ A := by
    exact (mem_inter.mp (show a ∈ A ∩ R.P by rw [ha]; simp)).1
  have hbA : b ∈ A := by
    exact (mem_inter.mp (show b ∈ A ∩ R.Q by rw [hb]; simp)).1
  have hUc : U.card = 4 := by
    dsimp [U]
    rw [card_sdiff, R.P_meet, h.1 R.P R.P_mem]
  have hVc : V.card = 4 := by
    dsimp [V]
    rw [card_sdiff, R.Q_meet, h.1 R.Q R.Q_mem]
  have hPc : R.P = insert a U := split_singleton ha
  have hQc : R.Q = insert b V := split_singleton hb
  have htracec (i : Fin 4) : (trace i).card = 3 := by
    dsimp [trace]
    rw [card_sdiff, R.double_meet, h.1 _ (R.double_mem i)]
  have hleft : ∀ x ∈ A, ∀ y ∈ X,
      (∃ i, x ∈ edge i ∧ y ∈ trace i) ∨
        (x = a ∧ y ∈ U) ∨ (x = b ∧ y ∈ V) := by
    intro x hx y hy
    have hyA : y ∉ A := (mem_sdiff.mp hy).2
    have hxy : x ≠ y := by intro he; exact hyA (he ▸ hx)
    obtain ⟨E, hE, hxE, hyE⟩ := pair_cover_block h.2 hxy
    rcases (R.mem_iff E).mp hE with rfl | rfl | rfl | ⟨i, rfl⟩
    · exact False.elim (hyA hyE)
    · right; left
      refine ⟨?_, mem_sdiff.mpr ⟨hyE, hyA⟩⟩
      exact mem_singleton.mp (ha ▸ mem_inter.mpr ⟨hx, hxE⟩)
    · right; right
      refine ⟨?_, mem_sdiff.mpr ⟨hyE, hyA⟩⟩
      exact mem_singleton.mp (hb ▸ mem_inter.mpr ⟨hx, hxE⟩)
    · exact Or.inl ⟨i, mem_inter.mpr ⟨hx, hxE⟩, mem_sdiff.mpr ⟨hyE, hyA⟩⟩
  have hright : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      (∃ i, x ∈ trace i ∧ y ∈ trace i) ∨
        (x ∈ U ∧ y ∈ U) ∨ (x ∈ V ∧ y ∈ V) := by
    intro x hx y hy hxy
    have hxA : x ∉ A := (mem_sdiff.mp hx).2
    have hyA : y ∉ A := (mem_sdiff.mp hy).2
    obtain ⟨E, hE, hxE, hyE⟩ := pair_cover_block h.2 hxy
    rcases (R.mem_iff E).mp hE with rfl | rfl | rfl | ⟨i, rfl⟩
    · exact False.elim (hxA hxE)
    · exact Or.inr (Or.inl ⟨mem_sdiff.mpr ⟨hxE, hxA⟩, mem_sdiff.mpr ⟨hyE, hyA⟩⟩)
    · exact Or.inr (Or.inr ⟨mem_sdiff.mpr ⟨hxE, hxA⟩, mem_sdiff.mpr ⟨hyE, hyA⟩⟩)
    · exact Or.inl ⟨i, mem_sdiff.mpr ⟨hxE, hxA⟩, mem_sdiff.mpr ⟨hyE, hyA⟩⟩
  have hedgedeg : ∀ x ∈ A,
      (univ.filter fun i => x ∈ edge i).card +
        (if x = a then 1 else 0) + (if x = b then 1 else 0) = 2 := by
    intro x hx
    have hxp : x ∈ R.P ↔ x = a := by
      have hh : x ∈ A ∩ R.P ↔ x = a := by rw [ha]; simp
      simpa only [mem_inter, hx, true_and] using hh
    have hxq : x ∈ R.Q ↔ x = b := by
      have hh : x ∈ A ∩ R.Q ↔ x = b := by rw [hb]; simp
      simpa only [mem_inter, hx, true_and] using hh
    have hs := R.degree_split hAc x
    rw [hlow x hx] at hs
    simp only [hx, ite_true, hxp, hxq] at hs
    simp only [edge, mem_inter, hx, true_and]
    omega
  have hrightdeg : ∀ x ∈ X,
      3 ≤ (univ.filter fun i => x ∈ trace i).card +
        (if x ∈ U then 1 else 0) + (if x ∈ V then 1 else 0) := by
    intro x hx
    have hxA : x ∉ A := (mem_sdiff.mp hx).2
    have hs := R.degree_split hAc x
    have hl := degree_at_least_three_11_5_2 hn h x
    simp only [hxA, ite_false, zero_add] at hs
    simp only [trace, U, V, mem_sdiff, hxA, not_false_eq_true, and_true]
    omega
  have hmeet : ∀ i j, i ≠ j → (edge i ∩ edge j).Nonempty →
      trace j = X \ trace i := by
    intro i j hij hm
    obtain ⟨x, hx⟩ := hm
    obtain ⟨hxi, hxj⟩ := mem_inter.mp hx
    obtain ⟨hxA, hxBi⟩ := mem_inter.mp hxi
    have hxBj := (mem_inter.mp hxj).2
    exact structural_trace_complement hn h hA (R.double_mem i) (R.double_mem j)
      (R.A_ne_double hAc i) (R.A_ne_double hAc j)
      (fun he => hij (R.injective he)) hxA hxBi hxBj (hlow x hxA)
      (R.double_meet i) (R.double_meet j)
  let S : SixBlockFrame α := {
    A := A
    X := X
    cardA := hAc
    cardX := hXc
    edge := edge
    trace := trace
    edge_subset := fun _ => inter_subset_left
    trace_subset := fun _ => sdiff_subset_sdiff (subset_univ _) Subset.rfl
    edge_card := R.double_meet
    trace_card := htracec
    meet_complement := hmeet
    no_single := no_single_trace_of_right_cover hXc hUc hVc hright
    disjointAX := disjoint_sdiff_self_right
    spans := union_sdiff_of_subset (subset_univ _)
    a := a
    b := b
    a_mem := haA
    b_mem := hbA
    U := U
    V := V
    U_subset := sdiff_subset_sdiff (subset_univ _) Subset.rfl
    V_subset := sdiff_subset_sdiff (subset_univ _) Subset.rfl
    U_card := hUc
    V_card := hVc
    edge_degree := hedgedeg
    right_degree := hrightdeg
    left_cover := hleft
    right_cover := hright }
  refine ⟨S, rfl, ?_⟩
  ext E
  rw [S.mem_family, R.mem_iff]
  change (E = A ∨ (∃ i, E = (A ∩ R.double i) ∪ (R.double i \ A)) ∨
    E = insert a U ∨ E = insert b V) ↔ _
  simp only [split_block, ← hPc, ← hQc]
  tauto

/-- The six-block frame exists for every seven-block (11,5,2) covering. -/
theorem exists_six_block_frame {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7) :
    ∃ S : SixBlockFrame α, S.family = C := by
  obtain ⟨A, hA, hlow⟩ := structural_all_low_block hn h hC
  obtain ⟨S, _, hS⟩ := six_block_frame_of_low_block hn h hC hA hlow
  exact ⟨S, hS⟩

#guard_standard_axioms six_block_frame_of_low_block exists_six_block_frame

end CoveringDesigns.StantonStructural
