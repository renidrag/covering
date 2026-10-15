import CoveringDesigns.C12_6_3.Structural.Projection
import Mathlib.Tactic.FinCases

/-!
The six minimum points split into three complementary pairs. Their block
traces are exactly the empty set, the three pairs, the three complementary
four-sets, and the eight transversals. This is a structural deduction from
the incidence moments, not an enumeration of covering families.
-/

namespace CoveringDesigns.GPPTStructural

open Finset

variable {α : Type*} [DecidableEq α]

structure ThreePairPartition (P : Finset α) where
  pairs : Fin 3 → Finset α
  pairs_card : ∀ i, (pairs i).card = 2
  pairs_subset : ∀ i, pairs i ⊆ P
  pairs_disjoint : Pairwise fun i j => Disjoint (pairs i) (pairs j)
  pairs_union : univ.biUnion pairs = P

/-- The three-point subsets selecting one point from each pair. -/
def pairTransversals (P : Finset α) (E : Fin 3 → Finset α) : Family α :=
  (P.powersetCard 3).filter fun T => ∀ i, (T ∩ E i).card = 1

/-- The exact low-point projection, including uniqueness of every row. -/
structure LowProjectionFrame [Fintype α] (C : Family α)
    extends ThreePairPartition (minimumPoints C 7) where
  trace_injective : Set.InjOn (fun B => minimumPoints C 7 ∩ B) C
  traces_eq : C.image (fun B => minimumPoints C 7 ∩ B) =
    insert ∅ ((univ.image pairs) ∪
      (univ.image fun i => minimumPoints C 7 \ pairs i) ∪
      pairTransversals (minimumPoints C 7) pairs)

namespace ThreePairPartition

variable {P : Finset α} (F : ThreePairPartition P)

theorem pairs_nonempty (i : Fin 3) : (F.pairs i).Nonempty :=
  card_pos.mp (by rw [F.pairs_card]; omega)

theorem pairs_injective : Function.Injective F.pairs := by
  intro i j he
  by_contra hn
  obtain ⟨x, hx⟩ := F.pairs_nonempty i
  exact disjoint_left.mp (F.pairs_disjoint hn) hx (he ▸ hx)

theorem intersection_sum {T : Finset α} (hT : T ⊆ P) :
    (∑ i, (T ∩ F.pairs i).card) = T.card := by
  have he : univ.biUnion (fun i => T ∩ F.pairs i) = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
      exact (mem_inter.mp hi).1
    · intro hx
      have hp := hT hx
      rw [← F.pairs_union] at hp
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
      exact mem_biUnion.mpr ⟨i, mem_univ _, mem_inter.mpr ⟨hx, hi⟩⟩
  have hd : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (fun i => T ∩ F.pairs i) := by
    intro i _ j _ hij
    exact (F.pairs_disjoint hij).mono inter_subset_right inter_subset_right
  have hc := card_biUnion hd
  rw [he] at hc
  exact hc.symm

theorem four_card (hP : P.card = 6) (i : Fin 3) : (P \ F.pairs i).card = 4 := by
  rw [card_sdiff_of_subset (F.pairs_subset i), hP, F.pairs_card]

theorem pair_subset_complement {i j : Fin 3} (hij : i ≠ j) :
    F.pairs i ⊆ P \ F.pairs j := by
  intro x hx
  exact mem_sdiff.mpr ⟨F.pairs_subset i hx, disjoint_left.mp (F.pairs_disjoint hij) hx⟩

theorem pair_not_subset_own_complement (i : Fin 3) : ¬ F.pairs i ⊆ P \ F.pairs i := by
  intro hs
  obtain ⟨x, hx⟩ := F.pairs_nonempty i
  exact (mem_sdiff.mp (hs hx)).2 hx

/-- A triple meeting every pair has precisely one point in each. -/
theorem transversal_of_meets {T : Finset α} (hT : T ⊆ P) (ht : T.card = 3)
    (hmeet : ∀ i, (T ∩ F.pairs i).Nonempty) :
    T ∈ pairTransversals P F.pairs := by
  have hs := F.intersection_sum hT
  rw [ht] at hs
  refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hT, ht⟩, ?_⟩
  intro i
  have hlo (j : Fin 3) : 1 ≤ (T ∩ F.pairs j).card := card_pos.mpr (hmeet j)
  have hsum : (∑ j : Fin 3, (1 : ℕ)) = 3 := by simp
  by_contra hn
  have hlt : (∑ j : Fin 3, (1 : ℕ)) < ∑ j : Fin 3, (T ∩ F.pairs j).card := by
    apply sum_lt_sum (fun j _ => hlo j)
    exact ⟨i, mem_univ _, by have := hlo i; omega⟩
  omega

end ThreePairPartition

private structure FourProjection [Fintype α] (C : Family α)
    extends ThreePairPartition (minimumPoints C 7) where
  four : Fin 3 → Finset α
  four_injective : Function.Injective four
  four_mem : ∀ i, four i ∈ C
  four_trace : ∀ i, minimumPoints C 7 ∩ four i = minimumPoints C 7 \ pairs i
  four_complete : ∀ B ∈ C, (minimumPoints C 7 ∩ B).card = 4 → ∃ i, four i = B

private theorem exists_four_projection [Fintype α] {C : Family α}
    (hP : (minimumPoints C 7).card = 6)
    (hno : NoDuplicateMinimumTriple C) (hfour : lowBlockCount C 4 = 3) :
    Nonempty (FourProjection C) := by
  let P := minimumPoints C 7
  have hP6 : P.card = 6 := hP
  let D := C.filter fun B => (P ∩ B).card = 4
  have hD : D.card = 3 := hfour
  let e : D ≃ Fin 3 := Finset.equivFinOfCardEq hD
  let B (i : Fin 3) : Finset α := (e.symm i).val
  have hBi : Function.Injective B := by
    intro i j he
    exact e.symm.injective (Subtype.ext he)
  have hBD (i : Fin 3) : B i ∈ D := (e.symm i).property
  have hBC (i : Fin 3) : B i ∈ C := (mem_filter.mp (hBD i)).1
  have hBT (i : Fin 3) : (P ∩ B i).card = 4 := (mem_filter.mp (hBD i)).2
  let E (i : Fin 3) := P \ (P ∩ B i)
  have hE (i : Fin 3) : (E i).card = 2 := by
    dsimp only [E]
    rw [card_sdiff_of_subset inter_subset_left, hP, hBT]
  have hEP (i : Fin 3) : E i ⊆ P := sdiff_subset
  have hdis : Pairwise fun i j => Disjoint (E i) (E j) := by
    intro i j hij
    have hsmall := no_duplicate_common_minimum_card hno (hBC i) (hBC j)
      (fun he => hij (hBi he))
    change ((P ∩ B i) ∩ B j).card ≤ 2 at hsmall
    have hI : (P ∩ B i) ∩ (P ∩ B j) = (P ∩ B i) ∩ B j := by
      ext x
      simp only [mem_inter]
      tauto
    have hc := card_union_add_card_inter (P ∩ B i) (P ∩ B j)
    rw [hI, hBT, hBT] at hc
    have hsub : (P ∩ B i) ∪ (P ∩ B j) ⊆ P :=
      union_subset inter_subset_left inter_subset_left
    have heq : (P ∩ B i) ∪ (P ∩ B j) = P :=
      eq_of_subset_of_card_le hsub (by omega)
    apply disjoint_left.mpr
    intro x hx hy
    have hp := (mem_sdiff.mp hx).1
    rw [← heq] at hp
    rcases mem_union.mp hp with hx' | hy'
    · exact (mem_sdiff.mp hx).2 hx'
    · exact (mem_sdiff.mp hy).2 hy'
  have hEU : univ.biUnion E = P := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
      exact hEP i hi
    · have hd : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint E :=
        fun _ _ _ _ hij => hdis hij
      rw [card_biUnion hd]
      simp [hE, hP6]
  refine ⟨⟨⟨E, hE, hEP, hdis, hEU⟩, B, hBi, hBC, ?_, ?_⟩⟩
  · intro i
    ext x
    simp only [E, mem_sdiff, mem_inter]
    tauto
  · intro A hA ht
    have hAD : A ∈ D := mem_filter.mpr ⟨hA, ht⟩
    exact ⟨e ⟨A, hAD⟩, by simp [B]⟩

namespace FourProjection

variable [Fintype α] {C : Family α} (F : FourProjection C)

private theorem four_trace_card (hP : (minimumPoints C 7).card = 6) (i : Fin 3) :
    (minimumPoints C 7 ∩ F.four i).card = 4 := by
  rw [F.four_trace, F.toThreePairPartition.four_card hP]

/-- A triple trace cannot miss a pair, since it would then repeat a triple
inside the complementary four-point trace. -/
private theorem triple_transversal (hP : (minimumPoints C 7).card = 6)
    (hno : NoDuplicateMinimumTriple C) {B : Finset α} (hB : B ∈ C)
    (ht : (minimumPoints C 7 ∩ B).card = 3) :
    minimumPoints C 7 ∩ B ∈ pairTransversals (minimumPoints C 7) F.pairs := by
  apply F.toThreePairPartition.transversal_of_meets inter_subset_left ht
  intro i
  by_contra hn
  have hsub : minimumPoints C 7 ∩ B ⊆ F.four i := by
    intro x hx
    have hc : x ∈ minimumPoints C 7 \ F.pairs i := by
      refine mem_sdiff.mpr ⟨(mem_inter.mp hx).1, ?_⟩
      intro hi
      exact hn ⟨x, mem_inter.mpr ⟨hx, hi⟩⟩
    rw [← F.four_trace] at hc
    exact (mem_inter.mp hc).2
  have hne : B ≠ F.four i := by
    intro he
    rw [he, F.four_trace_card hP] at ht
    omega
  have hc := no_duplicate_common_minimum_card hno hB (F.four_mem i) hne
  rw [inter_eq_left.mpr hsub, ht] at hc
  omega

/-- Coverage supplies every transversal, and no four-point trace can contain
it. Its covering block consequently has exactly that three-point trace. -/
private theorem transversal_occurs (hC : IsCover C 6 3)
    (hle : ∀ B ∈ C, (minimumPoints C 7 ∩ B).card ≤ 4)
    {T : Finset α} (hT : T ∈ pairTransversals (minimumPoints C 7) F.pairs) :
    ∃ B ∈ C, minimumPoints C 7 ∩ B = T := by
  obtain ⟨hpower, hone⟩ := mem_filter.mp hT
  obtain ⟨hTP, ht⟩ := mem_powersetCard.mp hpower
  obtain ⟨B, hB, hTB⟩ := hC.2 T ht
  have hsub : T ⊆ minimumPoints C 7 ∩ B := subset_inter hTP hTB
  have hlo := card_le_card hsub
  have hhi := hle B hB
  have hn4 : (minimumPoints C 7 ∩ B).card ≠ 4 := by
    intro h4
    obtain ⟨i, rfl⟩ := F.four_complete B hB h4
    obtain ⟨x, hx⟩ := card_pos.mp (by rw [hone i]; omega)
    have hm := hsub (mem_inter.mp hx).1
    rw [F.four_trace] at hm
    exact (mem_sdiff.mp hm).2 (mem_inter.mp hx).2
  exact ⟨B, hB, (eq_of_subset_of_card_le hsub (by omega)).symm⟩

private def pairResidual (i : Fin 3) : Family α :=
  (C.filter (F.pairs i ⊆ ·)) \ ((univ.erase i).image F.four)

private theorem pair_container_card
    (hpairs : ∀ p q, degree C p = 7 → degree C q = 7 → p ≠ q →
      degree (star C p) q = 3) (i : Fin 3) :
    (C.filter (F.pairs i ⊆ ·)).card = 3 := by
  obtain ⟨p, q, hpq, he⟩ := card_eq_two.mp (F.pairs_card i)
  change containmentCount C (F.pairs i) = 3
  rw [he, containmentCount_pair]
  apply hpairs p q
  · exact (mem_filter.mp (F.pairs_subset i (by rw [he]; simp))).2
  · exact (mem_filter.mp (F.pairs_subset i (by rw [he]; simp))).2
  · exact hpq

private theorem other_four_subset (i : Fin 3) :
    (univ.erase i).image F.four ⊆ C.filter (F.pairs i ⊆ ·) := by
  intro B hB
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hB
  refine mem_filter.mpr ⟨F.four_mem j, ?_⟩
  intro x hx
  have hm := F.toThreePairPartition.pair_subset_complement
    (Ne.symm (mem_erase.mp hj).1) hx
  rw [← F.four_trace] at hm
  exact (mem_inter.mp hm).2

private theorem pairResidual_card
    (hpairs : ∀ p q, degree C p = 7 → degree C q = 7 → p ≠ q →
      degree (star C p) q = 3) (i : Fin 3) : (F.pairResidual i).card = 1 := by
  rw [pairResidual, card_sdiff_of_subset (F.other_four_subset i),
    F.pair_container_card hpairs, card_image_of_injective _ F.four_injective,
    card_erase_of_mem (mem_univ i), card_univ]
  rfl

private theorem mem_pairResidual_iff (hP : (minimumPoints C 7).card = 6)
    (hno : NoDuplicateMinimumTriple C)
    (hle : ∀ B ∈ C, (minimumPoints C 7 ∩ B).card ≤ 4)
    (i : Fin 3) (B : Finset α) :
    B ∈ F.pairResidual i ↔ B ∈ C ∧ minimumPoints C 7 ∩ B = F.pairs i := by
  constructor
  · intro hB
    obtain ⟨hm, hn⟩ := mem_sdiff.mp hB
    obtain ⟨hBC, hEB⟩ := mem_filter.mp hm
    have hsub : F.pairs i ⊆ minimumPoints C 7 ∩ B :=
      subset_inter (F.pairs_subset i) hEB
    have hge := card_le_card hsub
    rw [F.pairs_card] at hge
    have hhi := hle B hBC
    have hn4 : (minimumPoints C 7 ∩ B).card ≠ 4 := by
      intro hc
      obtain ⟨j, rfl⟩ := F.four_complete B hBC hc
      by_cases hij : j = i
      · subst j
        apply F.toThreePairPartition.pair_not_subset_own_complement i
        rwa [F.four_trace] at hsub
      · exact hn (mem_image.mpr ⟨j, mem_erase.mpr ⟨hij, mem_univ _⟩, rfl⟩)
    have hn3 : (minimumPoints C 7 ∩ B).card ≠ 3 := by
      intro hc
      have hh := (mem_filter.mp (F.triple_transversal hP hno hBC hc)).2 i
      rw [inter_eq_right.mpr hsub, F.pairs_card] at hh
      omega
    exact ⟨hBC, (eq_of_subset_of_card_le hsub (by rw [F.pairs_card]; omega)).symm⟩
  · rintro ⟨hB, he⟩
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hB, ?_⟩, ?_⟩
    · rw [← he]
      exact inter_subset_right
    · intro hm
      obtain ⟨j, _, hBj⟩ := mem_image.mp hm
      have hc := congrArg Finset.card he
      rw [← hBj, F.four_trace_card hP, F.pairs_card] at hc
      omega

/-- Each matching pair occurs as a trace exactly once. Its other two
occurrences already lie in the two complementary four-point rows. -/
private theorem pair_occurs_unique (hP : (minimumPoints C 7).card = 6)
    (hno : NoDuplicateMinimumTriple C)
    (hle : ∀ B ∈ C, (minimumPoints C 7 ∩ B).card ≤ 4)
    (hpairs : ∀ p q, degree C p = 7 → degree C q = 7 → p ≠ q →
      degree (star C p) q = 3) (i : Fin 3) :
    ∃! B, B ∈ C ∧ minimumPoints C 7 ∩ B = F.pairs i := by
  have hh := card_eq_one_iff_existsUnique.mp (F.pairResidual_card hpairs i)
  simpa only [F.mem_pairResidual_iff hP hno hle] using hh

end FourProjection

/-- The no-duplicate branch has exactly the standard matching projection on
its six minimum points. The pair-degree premise is GPPT Lemma 5.2. -/
theorem exists_low_projection_frame [Fintype α] {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card = 15)
    (hno : NoDuplicateMinimumTriple C)
    (hpairs : ∀ p q, degree C p = 7 → degree C q = 7 → p ≠ q →
      degree (star C p) q = 3) : Nonempty (LowProjectionFrame C) := by
  classical
  have hP := no_duplicate_minimum_points_card hn hC hb hno
  obtain ⟨h0, h1, h2, _, h4⟩ := no_duplicate_low_histogram hn hC hb hno hpairs
  obtain ⟨F⟩ := exists_four_projection hP hno h4
  have hle (B : Finset α) (hB : B ∈ C) :=
    no_duplicate_block_minimum_card hno hpairs hB
  have hex (i : Fin 3) := F.pair_occurs_unique hP hno hle hpairs i
  choose pairBlock hpairBlock hpairUnique using hex
  have hpairInj : Function.Injective pairBlock := by
    intro i j he
    apply F.toThreePairPartition.pairs_injective
    rw [← (hpairBlock i).2, ← (hpairBlock j).2, he]
  have hpairFamily : C.filter (fun B => (minimumPoints C 7 ∩ B).card = 2) =
      univ.image pairBlock := by
    symm
    apply eq_of_subset_of_card_le
    · intro B hB
      obtain ⟨i, _, rfl⟩ := mem_image.mp hB
      exact mem_filter.mpr ⟨(hpairBlock i).1, by rw [(hpairBlock i).2, F.pairs_card]⟩
    · rw [card_image_of_injective _ hpairInj, card_univ]
      change lowBlockCount C 2 ≤ 3
      omega
  have hnone (B : Finset α) (hB : B ∈ C) :
      (minimumPoints C 7 ∩ B).card ≠ 1 := by
    intro hh
    have hm : B ∈ C.filter (fun D => (minimumPoints C 7 ∩ D).card = 1) :=
      mem_filter.mpr ⟨hB, hh⟩
    have he : C.filter (fun D => (minimumPoints C 7 ∩ D).card = 1) = ∅ :=
      card_eq_zero.mp h1
    rw [he] at hm
    exact notMem_empty _ hm
  have htraceInjective : Set.InjOn (fun B => minimumPoints C 7 ∩ B) C := by
    intro B hB D hD he
    change minimumPoints C 7 ∩ B = minimumPoints C 7 ∩ D at he
    have hecard := congrArg Finset.card he
    by_cases hh : 3 ≤ (minimumPoints C 7 ∩ B).card
    · by_contra hne
      have hsub : minimumPoints C 7 ∩ B ⊆ D := by
        rw [he]
        exact inter_subset_right
      have hc := no_duplicate_common_minimum_card hno hB hD hne
      rw [inter_eq_left.mpr hsub] at hc
      omega
    · have hn1 := hnone B hB
      have hcases : (minimumPoints C 7 ∩ B).card = 0 ∨
          (minimumPoints C 7 ∩ B).card = 2 := by omega
      rcases hcases with hz | ht
      · have hc : (C.filter (fun E => (minimumPoints C 7 ∩ E).card = 0)).card ≤ 1 := by
          change lowBlockCount C 0 ≤ 1
          omega
        exact card_le_one.mp hc B (mem_filter.mpr ⟨hB, hz⟩)
          D (mem_filter.mpr ⟨hD, by omega⟩)
      · have hBm : B ∈ univ.image pairBlock := by
          rw [← hpairFamily]
          exact mem_filter.mpr ⟨hB, ht⟩
        have hDm : D ∈ univ.image pairBlock := by
          rw [← hpairFamily]
          exact mem_filter.mpr ⟨hD, by omega⟩
        obtain ⟨i, _, rfl⟩ := mem_image.mp hBm
        obtain ⟨j, _, rfl⟩ := mem_image.mp hDm
        have hij : i = j := F.toThreePairPartition.pairs_injective
          ((hpairBlock i).2.symm.trans (he.trans (hpairBlock j).2))
        exact congrArg pairBlock hij
  have hzeroExists : ∃ B ∈ C, minimumPoints C 7 ∩ B = ∅ := by
    have hpos : 0 < (C.filter (fun B => (minimumPoints C 7 ∩ B).card = 0)).card := by
      change 0 < lowBlockCount C 0
      omega
    obtain ⟨B, hB⟩ := card_pos.mp hpos
    exact ⟨B, (mem_filter.mp hB).1, card_eq_zero.mp (mem_filter.mp hB).2⟩
  refine ⟨⟨F.toThreePairPartition, htraceInjective, ?_⟩⟩
  ext T
  simp only [mem_insert, mem_union, mem_image]
  constructor
  · rintro ⟨B, hB, rfl⟩
    have hup := hle B hB
    have hn1 := hnone B hB
    have hcases : (minimumPoints C 7 ∩ B).card = 0 ∨
        (minimumPoints C 7 ∩ B).card = 2 ∨
        (minimumPoints C 7 ∩ B).card = 3 ∨
        (minimumPoints C 7 ∩ B).card = 4 := by omega
    rcases hcases with hz | htwo | hthree | hfour
    · exact Or.inl (card_eq_zero.mp hz)
    · have hm : B ∈ univ.image pairBlock := by
        rw [← hpairFamily]
        exact mem_filter.mpr ⟨hB, htwo⟩
      obtain ⟨i, _, rfl⟩ := mem_image.mp hm
      exact Or.inr (Or.inl (Or.inl ⟨i, mem_univ _, (hpairBlock i).2.symm⟩))
    · exact Or.inr (Or.inr (F.triple_transversal hP hno hB hthree))
    · obtain ⟨i, rfl⟩ := F.four_complete B hB hfour
      exact Or.inr (Or.inl (Or.inr ⟨i, mem_univ _, (F.four_trace i).symm⟩))
  · rintro (rfl | (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ht)
    · exact hzeroExists
    · exact ⟨pairBlock i, (hpairBlock i).1, (hpairBlock i).2⟩
    · exact ⟨F.four i, F.four_mem i, F.four_trace i⟩
    · exact F.transversal_occurs hC hle ht

#guard_standard_axioms ThreePairPartition.intersection_sum
  ThreePairPartition.transversal_of_meets exists_low_projection_frame

#print axioms exists_low_projection_frame

end CoveringDesigns.GPPTStructural
