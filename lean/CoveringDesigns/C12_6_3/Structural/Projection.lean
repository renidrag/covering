import CoveringDesigns.C12_6_3.Structural.Moments

/-! The six-point projection in the no-duplicate branch of GPPT 5.9.
The pair-multiplicity hypothesis is kept explicit here; it is GPPT 5.2.
No covering configurations are enumerated. -/

namespace CoveringDesigns.GPPTStructural

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Distinct blocks cannot share three minimum points in this branch. -/
theorem no_duplicate_common_minimum_card {C : Family α}
    (hno : NoDuplicateMinimumTriple C) {B D : Finset α}
    (hB : B ∈ C) (hD : D ∈ C) (hne : B ≠ D) :
    ((minimumPoints C 7 ∩ B) ∩ D).card ≤ 2 := by
  by_contra h
  obtain ⟨T, hT, ht⟩ := exists_subset_card_eq (by omega :
    3 ≤ ((minimumPoints C 7 ∩ B) ∩ D).card)
  have hd : ∀ p ∈ T, degree C p = 7 := by
    intro p hp
    exact (mem_filter.mp (mem_inter.mp (mem_inter.mp (hT hp)).1).1).2
  have hc := hno T ht hd
  apply hne
  apply card_le_one.mp hc B (mem_filter.mpr ⟨hB, ?_⟩) D (mem_filter.mpr ⟨hD, ?_⟩)
  · intro p hp
    exact (mem_inter.mp (mem_inter.mp (hT hp)).1).2
  · intro p hp
    exact (mem_inter.mp (hT hp)).2

/-- A block has at most four minimum points. Fix one such point p. Each
other minimum point in the block occurs with p in two of the other six
p-blocks, and each of those blocks can contain at most one such point. -/
theorem no_duplicate_block_minimum_card {C : Family α}
    (hno : NoDuplicateMinimumTriple C)
    (hpairs : ∀ p q, degree C p = 7 → degree C q = 7 → p ≠ q →
      degree (star C p) q = 3)
    {B : Finset α} (hB : B ∈ C) : (minimumPoints C 7 ∩ B).card ≤ 4 := by
  by_cases he : minimumPoints C 7 ∩ B = ∅
  · simp [he]
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr he
  have hpd : degree C p = 7 := (mem_filter.mp (mem_inter.mp hp).1).2
  have hpB : p ∈ B := (mem_inter.mp hp).2
  have hBs : B ∈ star C p := mem_filter.mpr ⟨hB, hpB⟩
  let S := (minimumPoints C 7 ∩ B).erase p
  have hSB : S ⊆ B := fun q hq => (mem_inter.mp (mem_of_mem_erase hq)).2
  have hsmall : ∀ D ∈ (star C p).erase B, (S ∩ D).card ≤ 1 := by
    intro D hD
    obtain ⟨hDB, hDs⟩ := mem_erase.mp hD
    obtain ⟨hDC, hpD⟩ := mem_filter.mp hDs
    have hbound := no_duplicate_common_minimum_card hno hB hDC hDB.symm
    have hset : ((minimumPoints C 7 ∩ B) ∩ D).erase p = S ∩ D := by
      ext q
      simp [S, and_assoc, and_comm]
    have hpm : p ∈ (minimumPoints C 7 ∩ B) ∩ D := mem_inter.mpr ⟨hp, hpD⟩
    have hc := card_erase_of_mem hpm
    rw [hset] at hc
    omega
  have hsum : (∑ q ∈ S, degree (star C p) q) = 3 * S.card := by
    have hdeg : ∀ q ∈ S, degree (star C p) q = 3 := by
      intro q hq
      have hdq := (mem_filter.mp (mem_inter.mp (mem_of_mem_erase hq)).1).2
      exact hpairs p q hpd hdq (ne_of_mem_erase hq).symm
    simpa [Nat.mul_comm] using sum_const_nat hdeg
  have htotal := point_incidence_moment (star C p) S
  rw [hsum] at htotal
  have hrest := sum_le_sum hsmall
  have hcard : ((star C p).erase B).card = 6 := by
    rw [card_erase_of_mem hBs]
    change degree C p - 1 = 6
    omega
  have hrest' : (∑ D ∈ (star C p).erase B, (S ∩ D).card) ≤ 6 := by
    simpa only [sum_const, Nat.nsmul_eq_mul, Nat.mul_one, hcard] using hrest
  have heq := sum_erase_add (star C p) (fun D => (S ∩ D).card) hBs
  rw [inter_eq_left.mpr hSB, ← htotal] at heq
  have hsc : S.card + 1 = (minimumPoints C 7 ∩ B).card := by
    dsimp [S]
    exact card_erase_add_one hp
  omega

/-- Number of blocks with precisely i minimum points. -/
def lowBlockCount (C : Family α) (i : ℕ) : ℕ :=
  (C.filter (fun B => (minimumPoints C 7 ∩ B).card = i)).card

theorem lowBlockCount_moment {C : Family α}
    (hle : ∀ B ∈ C, (minimumPoints C 7 ∩ B).card ≤ 4) (f : ℕ → ℕ) :
    (∑ i : Fin 5, lowBlockCount C i.val * f i.val) =
      ∑ B ∈ C, f (minimumPoints C 7 ∩ B).card := by
  simp only [lowBlockCount, card_eq_sum_ones, sum_filter, sum_mul, ite_mul,
    one_mul, zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro B hB
  let r : Fin 5 := ⟨(minimumPoints C 7 ∩ B).card, by have := hle B hB; omega⟩
  rw [sum_eq_single r]
  · simp [r]
  · intro i _ hir
    apply ite_eq_right
    intro h
    apply hir
    apply Fin.ext
    change i.val = (minimumPoints C 7 ∩ B).card
    simpa only [card_eq_sum_ones] using h.symm
  · simp

/-- The four incidence moments force the distribution 1,0,3,8,3. -/
theorem five_bin_moments (n : Fin 5 → ℕ)
    (h0 : ∑ i, n i = 15)
    (h1 : ∑ i, n i * i.val = 42)
    (h2 : ∑ i, n i * i.val.choose 2 = 45)
    (h3 : ∑ i, n i * i.val.choose 3 = 20) :
    n 0 = 1 ∧ n 1 = 0 ∧ n 2 = 3 ∧ n 3 = 8 ∧ n 4 = 3 := by
  simp only [Fin.sum_univ_succ] at h0 h1 h2 h3
  norm_num [Nat.choose] at h0 h1 h2 h3
  omega

omit [Fintype α] in
/-- Every triple of minimum points occurs exactly once in this branch. -/
theorem no_duplicate_triple_count {C : Family α}
    (hC : IsCover C 6 3) (hno : NoDuplicateMinimumTriple C)
    {T : Finset α} (ht : T.card = 3) (hd : ∀ p ∈ T, degree C p = 7) :
    containmentCount C T = 1 := by
  have hle := hno T ht hd
  obtain ⟨B, hB, hTB⟩ := hC.2 T ht
  have hpos : 0 < containmentCount C T :=
    card_pos.mpr ⟨B, mem_filter.mpr ⟨hB, hTB⟩⟩
  omega

/-- Incidence counting gives one all-high block, three low pairs, eight
low triples and three low four-sets. -/
theorem no_duplicate_low_histogram {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card = 15)
    (hno : NoDuplicateMinimumTriple C)
    (hpairs : ∀ p q, degree C p = 7 → degree C q = 7 → p ≠ q →
      degree (star C p) q = 3) :
    lowBlockCount C 0 = 1 ∧ lowBlockCount C 1 = 0 ∧
      lowBlockCount C 2 = 3 ∧ lowBlockCount C 3 = 8 ∧ lowBlockCount C 4 = 3 := by
  have hle := fun B hB => no_duplicate_block_minimum_card hno hpairs (B := B) hB
  have hP := no_duplicate_minimum_points_card hn hC hb hno
  apply five_bin_moments (fun i => lowBlockCount C i.val)
  · simpa [hb] using lowBlockCount_moment hle (fun _ => 1)
  · have h := lowBlockCount_moment hle id
    simp only [id_eq] at h
    rw [← point_incidence_moment] at h
    have hs : (∑ p ∈ minimumPoints C 7, degree C p) = 42 := by
      have hd : ∀ p ∈ minimumPoints C 7, degree C p = 7 :=
        fun _ hp => (mem_filter.mp hp).2
      simpa [hP] using sum_const_nat hd
    simpa only [id_eq, hs] using h
  · have h := lowBlockCount_moment hle (fun i => i.choose 2)
    rw [← containment_moment] at h
    have hs : (∑ T ∈ (minimumPoints C 7).powersetCard 2, containmentCount C T) = 45 := by
      have hd : ∀ T ∈ (minimumPoints C 7).powersetCard 2, containmentCount C T = 3 := by
        intro T hT
        obtain ⟨hsub, ht⟩ := mem_powersetCard.mp hT
        obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp ht
        rw [containmentCount_pair]
        apply hpairs p q
        · exact (mem_filter.mp (hsub (by simp))).2
        · exact (mem_filter.mp (hsub (by simp))).2
        · exact hpq
      simpa [card_powersetCard, hP, Nat.choose] using sum_const_nat hd
    exact h.trans hs
  · have h := lowBlockCount_moment hle (fun i => i.choose 3)
    rw [← containment_moment] at h
    have hs : (∑ T ∈ (minimumPoints C 7).powersetCard 3, containmentCount C T) = 20 := by
      have hd : ∀ T ∈ (minimumPoints C 7).powersetCard 3, containmentCount C T = 1 := by
        intro T hT
        obtain ⟨hsub, ht⟩ := mem_powersetCard.mp hT
        exact no_duplicate_triple_count hC hno ht (fun p hp => (mem_filter.mp (hsub hp)).2)
      simpa [card_powersetCard, hP, Nat.choose] using sum_const_nat hd
    exact h.trans hs

#guard_standard_axioms no_duplicate_common_minimum_card no_duplicate_block_minimum_card
  lowBlockCount_moment five_bin_moments no_duplicate_triple_count no_duplicate_low_histogram

end CoveringDesigns.GPPTStructural
