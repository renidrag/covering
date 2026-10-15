import CoveringDesigns.C11_5_2.SmallBounds
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

/-!
Structural intersection bounds for seven-block pair covers on eleven points.
All arguments use finite-set counting; there is no classification or finite
configuration checker in this module.
-/

namespace CoveringDesigns

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem pair_cover_block {C : Family α} (h : Covers C 2) {x y : α}
    (hne : x ≠ y) : ∃ B ∈ C, x ∈ B ∧ y ∈ B := by
  obtain ⟨B, hB, hs⟩ := h {x, y} (by simp [hne])
  exact ⟨B, hB, hs (by simp), hs (by simp)⟩

omit [Fintype α] in
/-- The three blocks through a degree-three point, with two prescribed. -/
theorem degree_three_third_block {C : Family α} {x : α} {A B : Finset α}
    (hd : degree C x = 3) (hA : A ∈ C) (hB : B ∈ C) (hAB : A ≠ B)
    (hxA : x ∈ A) (hxB : x ∈ B) :
    ∃ D ∈ C, D ≠ A ∧ D ≠ B ∧ x ∈ D ∧ star C x = {A, B, D} := by
  have hs : ({A, B} : Family α) ⊆ star C x := by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact mem_filter.mpr ⟨hA, hxA⟩
    · have : E = B := mem_singleton.mp hE
      subst E
      exact mem_filter.mpr ⟨hB, hxB⟩
  have hc := card_sdiff_add_card_eq_card hs
  have hpair : ({A, B} : Family α).card = 2 := by simp [hAB]
  have hthird : ((star C x) \ {A, B}).card = 1 := by
    change (star C x).card = 3 at hd
    omega
  obtain ⟨D, hD⟩ := card_eq_one.mp hthird
  have hDm : D ∈ (star C x) \ {A, B} := by rw [hD]; simp
  have hDC := (mem_filter.mp (mem_sdiff.mp hDm).1).1
  have hxD := (mem_filter.mp (mem_sdiff.mp hDm).1).2
  have hDA : D ≠ A := by intro he; subst D; simpa using (mem_sdiff.mp hDm).2
  have hDB : D ≠ B := by intro he; subst D; simpa using (mem_sdiff.mp hDm).2
  refine ⟨D, hDC, hDA, hDB, hxD, ?_⟩
  ext E
  constructor
  · intro hE
    by_cases hEAB : E ∈ ({A, B} : Family α)
    · simp only [mem_insert, mem_singleton] at hEAB ⊢
      tauto
    · have : E ∈ (star C x) \ {A, B} := mem_sdiff.mpr ⟨hE, hEAB⟩
      rw [hD] at this
      have : E = D := mem_singleton.mp this
      subst E
      simp
  · simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact mem_filter.mpr ⟨hA, hxA⟩
    · exact mem_filter.mpr ⟨hB, hxB⟩
    · exact mem_filter.mpr ⟨hDC, hxD⟩

theorem degree_three_star_union {C : Family α} {x : α} {A B D : Finset α}
    (h : Covers C 2) (hxA : x ∈ A) (hs : star C x = {A, B, D}) :
    A ∪ B ∪ D = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases he : x = y
  · subst y
    simp [hxA]
  · obtain ⟨E, hE, hxE, hyE⟩ := pair_cover_block h he
    have hm : E ∈ star C x := mem_filter.mpr ⟨hE, hxE⟩
    rw [hs] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> simp [hyE]

/-- Two blocks through a degree-three point meet in at most three points. -/
theorem degree_three_intersection_le_three {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2)
    {A B : Finset α} (hA : A ∈ C) (hB : B ∈ C) (hAB : A ≠ B)
    {x : α} (hxA : x ∈ A) (hxB : x ∈ B) (hd : degree C x = 3) :
    (A ∩ B).card ≤ 3 := by
  obtain ⟨D, hD, _, _, hxD, hs⟩ :=
    degree_three_third_block hd hA hB hAB hxA hxB
  have hall := degree_three_star_union h.2 hxA hs
  have hnonempty : 1 ≤ ((A ∪ B) ∩ D).card := by
    apply Nat.succ_le_of_lt
    exact card_pos.mpr ⟨x, by simp [hxA, hxD]⟩
  have hc1 := card_union_add_card_inter A B
  have hc2 := card_union_add_card_inter (A ∪ B) D
  rw [hall, card_univ, hn] at hc2
  have ha := h.1 A hA
  have hb := h.1 B hB
  have hd' := h.1 D hD
  omega

/-- The elementary incidence count already leaves at most two nonminimum points. -/
theorem structural_nonlow_card_le_two {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7) :
    (univ.filter fun x => degree C x ≠ 3).card ≤ 2 := by
  have hl := minimum_points_bound h.1 (degree_at_least_three_11_5_2 hn h)
  have hc := card_filter_add_card_filter_not (s := (univ : Finset α))
    (fun x => degree C x = 3)
  simp only [minimumPoints, hn, hC] at hl
  rw [card_univ, hn] at hc
  simp only [ne_eq]
  omega

/-- In any seven-block cover, two different blocks meet in at most three points. -/
theorem structural_intersection_le_three {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    {A B : Finset α} (hA : A ∈ C) (hB : B ∈ C) (hAB : A ≠ B) :
    (A ∩ B).card ≤ 3 := by
  by_contra hb
  have hx : ∃ x ∈ A ∩ B, degree C x = 3 := by
    by_contra hh
    have hs : A ∩ B ⊆ univ.filter fun x => degree C x ≠ 3 := by
      intro x hx
      exact mem_filter.mpr ⟨mem_univ x, fun he => hh ⟨x, hx, he⟩⟩
    have hc := (card_le_card hs).trans (structural_nonlow_card_le_two hn h hC)
    omega
  obtain ⟨x, hx, hd⟩ := hx
  exact hb (degree_three_intersection_le_three hn h hA hB hAB
    (mem_inter.mp hx).1 (mem_inter.mp hx).2 hd)

private theorem cross_product_le_six (a b : ℕ) (h : a + b ≤ 5) : a * b ≤ 6 := by
  have hs := Nat.mul_le_mul h h
  nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]

private theorem cross_product_le_four (a b : ℕ) (h : a + b ≤ 4) : a * b ≤ 4 := by
  have hs := Nat.mul_le_mul h h
  nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]

omit [Fintype α] in
/-- A five-set covers at most six cross pairs of two disjoint sets, or four
when it contains a point outside both sets. -/
theorem cross_pairs_capacity {A B E : Finset α} (hAB : Disjoint A B)
    (hE : E.card = 5) {z : α} (hzA : z ∉ A) (hzB : z ∉ B) :
    ((A ∩ E) ×ˢ (B ∩ E)).card + (if z ∈ E then 2 else 0) ≤ 6 := by
  have hd : Disjoint (A ∩ E) (B ∩ E) :=
    hAB.mono inter_subset_left inter_subset_left
  have hu : (A ∩ E) ∪ (B ∩ E) ⊆ E :=
    union_subset inter_subset_right inter_subset_right
  have hc := card_le_card hu
  rw [card_union_of_disjoint hd, hE] at hc
  rw [card_product]
  split_ifs with hzE
  · have hz : z ∉ (A ∩ E) ∪ (B ∩ E) := by simp [hzA, hzB]
    have hs : insert z ((A ∩ E) ∪ (B ∩ E)) ⊆ E :=
      insert_subset hzE hu
    have hc' := card_le_card hs
    rw [card_insert_of_notMem hz, card_union_of_disjoint hd, hE] at hc'
    have hb := cross_product_le_four (A ∩ E).card (B ∩ E).card (by omega)
    omega
  · simpa using cross_product_le_six (A ∩ E).card (B ∩ E).card hc

/-- Two different blocks of a seven-block cover cannot be disjoint. -/
theorem structural_blocks_intersect {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    {A B : Finset α} (hA : A ∈ C) (hB : B ∈ C) (hAB : A ≠ B) :
    (A ∩ B).Nonempty := by
  by_contra hh
  have hd : Disjoint A B := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hh)
  have ha := h.1 A hA
  have hb := h.1 B hB
  have hABcard : (A ∪ B).card = 10 := by rw [card_union_of_disjoint hd, ha, hb]
  have hout : ((univ : Finset α) \ (A ∪ B)).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn, hABcard]
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < ((univ : Finset α) \ (A ∪ B)).card by omega)
  have hzA : z ∉ A := fun hzA => (mem_sdiff.mp hz).2 (mem_union_left B hzA)
  have hzB : z ∉ B := fun hzB => (mem_sdiff.mp hz).2 (mem_union_right A hzB)
  let R := (C.erase A).erase B
  have hR : R.card = 5 := by
    dsimp [R]
    rw [card_erase_of_mem (mem_erase.mpr ⟨hAB.symm, hB⟩), card_erase_of_mem hA, hC]
  let cross := fun E : Finset α => (A ∩ E) ×ˢ (B ∩ E)
  have hcover : A ×ˢ B ⊆ R.biUnion cross := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    have hne : x ≠ y := by intro he; subst y; exact disjoint_left.mp hd hx hy
    obtain ⟨E, hE, hxE, hyE⟩ := pair_cover_block h.2 hne
    have hEA : E ≠ A := by intro he; subst E; exact disjoint_left.mp hd hyE hy
    have hEB : E ≠ B := by intro he; subst E; exact disjoint_left.mp hd hx hxE
    apply mem_biUnion.mpr
    exact ⟨E, mem_erase.mpr ⟨hEB, mem_erase.mpr ⟨hEA, hE⟩⟩,
      mem_product.mpr ⟨mem_inter.mpr ⟨hx, hxE⟩, mem_inter.mpr ⟨hy, hyE⟩⟩⟩
  have h25 : 25 ≤ ∑ E ∈ R, (cross E).card := by
    have hc := (card_le_card hcover).trans card_biUnion_le
    simpa [card_product, ha, hb] using hc
  have hstar : R.filter (z ∈ ·) = star C z := by
    ext E
    simp only [R, star, mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨_, _, hEC⟩, hzE⟩
      exact ⟨hEC, hzE⟩
    · rintro ⟨hEC, hzE⟩
      exact ⟨⟨by intro he; subst E; exact hzB hzE,
        by intro he; subst E; exact hzA hzE, hEC⟩, hzE⟩
  have hdeg : (∑ E ∈ R, if z ∈ E then 2 else 0) = 2 * degree C z := by
    rw [← sum_filter]
    simp [hstar, degree, Nat.mul_comm]
  have hcap : (∑ E ∈ R, (cross E).card) + 2 * degree C z ≤ 30 := by
    have hc := sum_le_sum (s := R) (fun E hER =>
      cross_pairs_capacity hd (h.1 E (mem_of_mem_erase (mem_of_mem_erase hER))) hzA hzB)
    simpa [sum_add_distrib, hdeg, hR, cross] using hc
  have hdl := degree_at_least_three_11_5_2 hn h z
  omega

/-- The third block is forced when the first two leave four points uncovered. -/
theorem degree_three_forced_third {C : Family α}
    (h : IsCover C 5 2) {A B : Finset α} (hA : A ∈ C) (hB : B ∈ C)
    (hAB : A ≠ B) {x : α} (hxA : x ∈ A) (hxB : x ∈ B)
    (hd : degree C x = 3) (hy : ((univ : Finset α) \ (A ∪ B)).card = 4) :
    insert x ((univ : Finset α) \ (A ∪ B)) ∈ C := by
  obtain ⟨D, hD, _, _, hxD, hs⟩ :=
    degree_three_third_block hd hA hB hAB hxA hxB
  have hsub : (univ : Finset α) \ (A ∪ B) ⊆ D := by
    intro y hy
    have hyAB := (mem_sdiff.mp hy).2
    have hxy : x ≠ y := by intro he; subst y; exact hyAB (mem_union_left B hxA)
    obtain ⟨E, hE, hxE, hyE⟩ := pair_cover_block h.2 hxy
    have hm : E ∈ star C x := mem_filter.mpr ⟨hE, hxE⟩
    rw [hs] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact False.elim (hyAB (mem_union_left B hyE))
    · exact False.elim (hyAB (mem_union_right A hyE))
    · exact hyE
  have hins : insert x ((univ : Finset α) \ (A ∪ B)) ⊆ D := insert_subset hxD hsub
  have hxout : x ∉ (univ : Finset α) \ (A ∪ B) := by simp [hxA]
  have hcard : (insert x ((univ : Finset α) \ (A ∪ B))).card = 5 := by
    rw [card_insert_of_notMem hxout, hy]
  have he := eq_of_subset_of_card_le hins (by rw [hcard, h.1 D hD])
  rwa [he]

/-- A block of degree-three points meets each other block in at most two. -/
theorem structural_low_block_intersection_le_two {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    {A B : Finset α} (hA : A ∈ C) (hB : B ∈ C) (hAB : A ≠ B)
    (hlow : ∀ x ∈ A, degree C x = 3) : (A ∩ B).card ≤ 2 := by
  have hup := structural_intersection_le_three hn h hC hA hB hAB
  by_contra hh
  have hthree : (A ∩ B).card = 3 := by omega
  have hu := card_union_add_card_inter A B
  have ha := h.1 A hA
  have hb := h.1 B hB
  have hseven : (A ∪ B).card = 7 := by omega
  let Y := (univ : Finset α) \ (A ∪ B)
  have hycard : Y.card = 4 := by
    dsimp [Y]
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn, hseven]
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (show 1 < (A ∩ B).card by omega)
  have hxA := (mem_inter.mp hx).1
  have hyA := (mem_inter.mp hy).1
  have hxC : insert x Y ∈ C := degree_three_forced_third h hA hB hAB
    hxA (mem_inter.mp hx).2 (hlow x hxA) hycard
  have hyC : insert y Y ∈ C := degree_three_forced_third h hA hB hAB
    hyA (mem_inter.mp hy).2 (hlow y hyA) hycard
  have hne : insert x Y ≠ insert y Y := by
    intro he
    have hxm : x ∈ insert y Y := he ▸ mem_insert_self x Y
    rcases mem_insert.mp hxm with he | hout
    · exact hxy he
    · exact (mem_sdiff.mp hout).2 (mem_union_left B hxA)
  have hfour : 4 ≤ (insert x Y ∩ insert y Y).card := by
    rw [← hycard]
    apply card_le_card
    intro z hz
    exact mem_inter.mpr ⟨mem_insert_of_mem hz, mem_insert_of_mem hz⟩
  have hle := structural_intersection_le_three hn h hC hxC hyC hne
  omega

omit [Fintype α] in
/-- Count incidences with a fixed set by blocks or by points. -/
theorem block_intersection_sum (C : Family α) (A : Finset α) :
    ∑ B ∈ C, (A ∩ B).card = ∑ x ∈ A, degree C x := by
  have hc (B : Finset α) : (A ∩ B).card = ∑ x ∈ A, if x ∈ B then 1 else 0 := by
    rw [← sum_filter, ← card_eq_sum_ones]
    congr 1
  simp_rw [hc]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  simp only [degree, star, card_eq_sum_ones, sum_filter]

omit [Fintype α] in
theorem structural_low_block_intersection_sum {C : Family α}
    (h : IsCover C 5 2) {A : Finset α} (hA : A ∈ C)
    (hlow : ∀ x ∈ A, degree C x = 3) :
    ∑ B ∈ C.erase A, (A ∩ B).card = 10 := by
  have hs := block_intersection_sum C A
  have ha := h.1 A hA
  have hright : (∑ x ∈ A, degree C x) = 15 := by
    rw [sum_const_nat hlow, ha]
  rw [hright] at hs
  have he := sum_erase_add C (fun B => (A ∩ B).card) hA
  rw [inter_self, ha, hs] at he
  omega

/-- Exactly four other blocks meet a minimum-degree block twice; two meet once. -/
theorem structural_low_block_intersection_counts {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2) (hC : C.card = 7)
    {A : Finset α} (hA : A ∈ C) (hlow : ∀ x ∈ A, degree C x = 3) :
    ((C.erase A).filter (fun B => (A ∩ B).card = 2)).card = 4 ∧
    ((C.erase A).filter (fun B => (A ∩ B).card = 1)).card = 2 := by
  let R := C.erase A
  have hr : R.card = 6 := by dsimp [R]; rw [card_erase_of_mem hA, hC]
  have hsizes (B : Finset α) (hB : B ∈ R) :
      (A ∩ B).card = 1 ∨ (A ∩ B).card = 2 := by
    have hBC := mem_of_mem_erase hB
    have hAB : A ≠ B := (ne_of_mem_erase hB).symm
    have hupper := structural_low_block_intersection_le_two hn h hC hA hBC hAB hlow
    have hlower := card_pos.mpr (structural_blocks_intersect hn h hC hA hBC hAB)
    omega
  have hp : R.filter (fun B => ¬(A ∩ B).card = 1) =
      R.filter (fun B => (A ∩ B).card = 2) := by
    ext B
    simp only [mem_filter]
    constructor
    · rintro ⟨hB, hh⟩
      exact ⟨hB, (hsizes B hB).resolve_left hh⟩
    · rintro ⟨hB, hh⟩
      exact ⟨hB, by omega⟩
  have hc := card_filter_add_card_filter_not (s := R) (fun B => (A ∩ B).card = 1)
  rw [hp, hr] at hc
  have hsum : (∑ B ∈ R, (A ∩ B).card) =
      (R.filter (fun B => (A ∩ B).card = 1)).card +
      2 * (R.filter (fun B => (A ∩ B).card = 2)).card := by
    calc
      _ = ∑ B ∈ R, ((if (A ∩ B).card = 1 then 1 else 0) +
          (if (A ∩ B).card = 2 then 2 else 0)) := by
        apply sum_congr rfl
        intro B hB
        rcases hsizes B hB with hb | hb <;> simp [hb]
      _ = _ := by rw [sum_add_distrib, ← sum_filter, ← sum_filter]; simp [Nat.mul_comm]
  have hten := structural_low_block_intersection_sum h hA hlow
  change (∑ B ∈ R, (A ∩ B).card) = 10 at hten
  change (R.filter (fun B => (A ∩ B).card = 2)).card = 4 ∧
    (R.filter (fun B => (A ∩ B).card = 1)).card = 2
  omega

omit [Fintype α] in
/-- Any three different blocks through a minimum-degree point are its whole star. -/
theorem degree_three_specified_star {C : Family α} {x : α} {A B D : Finset α}
    (hd : degree C x = 3) (hA : A ∈ C) (hB : B ∈ C) (hD : D ∈ C)
    (hAB : A ≠ B) (hAD : A ≠ D) (hBD : B ≠ D)
    (hxA : x ∈ A) (hxB : x ∈ B) (hxD : x ∈ D) :
    star C x = {A, B, D} := by
  have hs : ({A, B, D} : Family α) ⊆ star C x := by
    intro E hE
    simp only [mem_insert, mem_singleton] at hE
    rcases hE with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨hA, hxA⟩
    · exact mem_filter.mpr ⟨hB, hxB⟩
    · exact mem_filter.mpr ⟨hD, hxD⟩
  apply (eq_of_subset_of_card_le hs _).symm
  change degree C x ≤ ({A, B, D} : Family α).card
  simp [hd, hAB, hAD, hBD]

/-- The outside traces of two double-intersection blocks sharing a minimum point
partition the six-point complement of the chosen block. -/
theorem structural_complementary_traces {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2)
    {A B D : Finset α} (hA : A ∈ C) (hB : B ∈ C) (hD : D ∈ C)
    (hAB : A ≠ B) (hAD : A ≠ D) (hBD : B ≠ D)
    {x : α} (hxA : x ∈ A) (hxB : x ∈ B) (hxD : x ∈ D)
    (hd : degree C x = 3) (hABtwo : (A ∩ B).card = 2)
    (hADtwo : (A ∩ D).card = 2) :
    (B \ A).card = 3 ∧ (D \ A).card = 3 ∧
    Disjoint (B \ A) (D \ A) ∧ (B \ A) ∪ (D \ A) = univ \ A := by
  have hs := degree_three_specified_star hd hA hB hD hAB hAD hBD hxA hxB hxD
  have hall := degree_three_star_union h.2 hxA hs
  have hu : (B \ A) ∪ (D \ A) = univ \ A := by
    ext y
    simp only [mem_union, mem_sdiff, mem_univ, true_and]
    constructor
    · rintro (⟨_, hy⟩ | ⟨_, hy⟩) <;> exact hy
    · intro hy
      have hm : y ∈ A ∪ B ∪ D := by rw [hall]; exact mem_univ y
      simp only [mem_union] at hm
      tauto
  have hb : (B \ A).card = 3 := by rw [card_sdiff, hABtwo, h.1 B hB]
  have hd' : (D \ A).card = 3 := by rw [card_sdiff, hADtwo, h.1 D hD]
  refine ⟨hb, hd', ?_, hu⟩
  have hucard : ((B \ A) ∪ (D \ A)).card = 6 := by
    rw [hu, card_sdiff_of_subset (subset_univ _), card_univ, hn, h.1 A hA]
  have hi := card_union_add_card_inter (B \ A) (D \ A)
  have hz : ((B \ A) ∩ (D \ A)).card = 0 := by omega
  exact disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hz)

theorem structural_trace_complement {C : Family α}
    (hn : Fintype.card α = 11) (h : IsCover C 5 2)
    {A B D : Finset α} (hA : A ∈ C) (hB : B ∈ C) (hD : D ∈ C)
    (hAB : A ≠ B) (hAD : A ≠ D) (hBD : B ≠ D)
    {x : α} (hxA : x ∈ A) (hxB : x ∈ B) (hxD : x ∈ D)
    (hd : degree C x = 3) (hABtwo : (A ∩ B).card = 2)
    (hADtwo : (A ∩ D).card = 2) :
    D \ A = (univ \ A) \ (B \ A) := by
  obtain ⟨_, _, hdisj, hu⟩ :=
    structural_complementary_traces hn h hA hB hD hAB hAD hBD hxA hxB hxD hd hABtwo hADtwo
  rw [← hu]
  ext y
  simp only [mem_sdiff, mem_union]
  constructor
  · intro hy
    exact ⟨Or.inr hy, fun hx => disjoint_left.mp hdisj (mem_sdiff.mpr hx) (mem_sdiff.mpr hy)⟩
  · rintro ⟨hy | hy, hx⟩
    · exact False.elim (hx hy)
    · exact hy

#guard_standard_axioms structural_blocks_intersect structural_intersection_le_three
  structural_low_block_intersection_le_two structural_low_block_intersection_counts
  structural_complementary_traces structural_trace_complement

end CoveringDesigns
