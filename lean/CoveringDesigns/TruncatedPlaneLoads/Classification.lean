import CoveringDesigns.TruncatedPlaneLoads.Counting

/-! Positive real equal-load classification for the derived support data. -/

namespace CoveringDesigns.TruncatedPlaneLoads.Internal.Loads
open Finset
variable {V G I : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable [Fintype I] {q : ℕ} {P : Plane q V G} {K : ℝ} (D : Loads (I := I) P K)

private theorem base_nonneg (i : G) : 0 ≤ D.baseMass i := by
  apply sum_nonneg
  intro j hj
  split_ifs
  · exact (D.extra_pos j).le
  · rfl

private theorem tip_nonneg (i : G) : 0 ≤ D.tipMass i := by
  apply sum_nonneg
  intro j hj
  split_ifs
  · exact (D.extra_pos j).le
  · rfl

private theorem weight_le_base (j : I) : D.weight j ≤ D.baseMass (D.base j) := by
  classical
  have h := single_le_sum (s := (univ : Finset I))
    (f := fun k => if D.base k = D.base j then D.weight k else 0)
    (fun k _ => by split_ifs; exact (D.extra_pos k).le; rfl) (mem_univ j)
  simpa [baseMass] using h

private theorem base_sum : (∑ i ∈ univ.image D.base, D.baseMass i) = D.extraMass := by
  classical
  unfold baseMass extraMass
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  simp [mem_image_of_mem D.base (mem_univ j)]

private theorem many_bases (hq : 0 < q) (hA : 0 < D.extraMass) :
    q ≤ (univ.image D.base).card := by
  classical
  have hb (i : G) : (q : ℝ) * D.baseMass i ≤ D.extraMass := by
    have he := D.group_equation i
    have hn := D.tip_nonneg i
    linarith
  have hs := sum_le_sum (s := univ.image D.base) (fun i _ => hb i)
  rw [← mul_sum, D.base_sum] at hs
  simp only [sum_const, nsmul_eq_mul] at hs
  have hr : (q : ℝ) ≤ ((univ.image D.base).card : ℝ) := by nlinarith
  exact_mod_cast hr

/-- The two descriptions of all positive equal loads on a supplied core,
after classifying the individual extra supports. -/
theorem classify (hq : 4 ≤ q) :
    (IsEmpty I ∧ ∀ E ∈ P.core, D.coreWeight E = K/q) ∨
    ∃ c : V, ∃ s : ℝ, 0 < s ∧ s < K/q ∧
      (∀ j, D.tip j = c ∧ D.base j ≠ P.group c ∧ D.weight j = s) ∧
      (∀ i, i ≠ P.group c → ∃ j, D.base j = i) ∧
      ∀ E ∈ P.core, D.coreWeight E = if c ∈ E then K/q-s else K/q := by
  classical
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqr
  rcases isEmpty_or_nonempty I with hI | hI
  · letI := hI
    refine Or.inl ⟨hI, fun E hE => ?_⟩
    have he := D.core_equation hE
    simp [edgeMass] at he
    apply (eq_div_iff hqne).mpr
    nlinarith
  · letI := hI
    have hA : 0 < D.extraMass :=
      sum_pos (fun j _ => D.extra_pos j) univ_nonempty
    obtain ⟨c, hc⟩ := common_coordinate P.group D.base D.tip D.outside D.meet
      (le_trans hq (D.many_bases (by omega) hA))
    have hpartition : D.baseMass (P.group c) + D.tipMass (P.group c) = D.extraMass := by
      unfold baseMass tipMass extraMass
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      rcases hc j with h | h
      · have hn := D.outside j
        simp [h] at hn ⊢
        simp [hn]
      · have hn := D.outside j
        rw [h] at hn
        simp [h, hn.symm]
    have hzero : D.baseMass (P.group c) = 0 := by
      have he := D.group_equation (P.group c)
      have hqr' : (4 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    have hb (j : I) : D.base j ≠ P.group c := by
      intro he
      have hl := D.weight_le_base j
      rw [he, hzero] at hl
      have hp := D.extra_pos j
      linarith
    have ht (j : I) : D.tip j = c := (hc j).resolve_left (hb j)
    have htip (i : G) (hi : i ≠ P.group c) : D.tipMass i = 0 := by
      simp [tipMass, ht, hi.symm]
    have hbase (i : G) (hi : i ≠ P.group c) : D.baseMass i = D.extraMass/q := by
      have he := D.group_equation i
      rw [htip i hi, add_zero] at he
      apply (eq_div_iff hqne).mpr
      nlinarith
    have hbinj : Function.Injective D.base := by
      intro j k hjk
      apply D.injective
      exact Prod.ext hjk ((ht j).trans (ht k).symm)
    have hw (j : I) : D.weight j = D.extraMass/q := by
      rw [← hbase (D.base j) (hb j)]
      unfold baseMass
      rw [sum_eq_single j]
      · simp
      · intro k hk hkj
        exact if_neg (fun h => hkj (hbinj h))
      · simp
    have hex (i : G) (hi : i ≠ P.group c) : ∃ j, D.base j = i := by
      by_contra hn
      push_neg at hn
      have hz : D.baseMass i = 0 := by simp [baseMass, hn]
      have he := D.group_equation i
      rw [hz, htip i hi] at he
      linarith
    have hew (E : Finset V) (hE : E ∈ P.core) :
        D.coreWeight E = if c ∈ E then K/q - D.extraMass/q else K/q := by
      have he := D.core_equation hE
      have hm : D.edgeMass E = if c ∈ E then D.extraMass else 0 := by
        by_cases hh : c ∈ E <;> simp [edgeMass, ht, hh, extraMass]
      rw [hm] at he
      split_ifs with hh
      · simp only [if_pos hh] at he
        apply (eq_sub_iff_add_eq).mpr
        apply (eq_div_iff hqne).mpr
        have hd := (div_mul_cancel₀ D.extraMass hqne)
        nlinarith
      · simp only [if_neg hh, add_zero] at he
        apply (eq_div_iff hqne).mpr
        nlinarith
    have hs : D.extraMass/q < K/q := by
      obtain ⟨E, hE⟩ := card_pos.mp (by rw [P.degree]; omega :
        0 < (P.core.filter (c ∈ ·)).card)
      have hp := D.core_pos E (mem_filter.mp hE).1
      rw [hew E (mem_filter.mp hE).1, if_pos (mem_filter.mp hE).2] at hp
      linarith
    exact Or.inr ⟨c, D.extraMass/q, div_pos hA hqr, hs,
      fun j => ⟨ht j, hb j, hw j⟩, hex, hew⟩

end CoveringDesigns.TruncatedPlaneLoads.Internal.Loads
