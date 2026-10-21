import CoveringDesigns.BoundaryRank.RestrictedEquality
import CoveringDesigns.TwoKMinusTwoEquality.Matrix

/-! The sixteen-row equality core, independently of covering assumptions.
All numerical and equality premises are explicit. -/
namespace CoveringDesigns.C18_10_3
open Finset Matrix Module
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The full nullity chain is tight; equality also saturates every positive
integer deficit. The graph structure is extracted in the next theorem. -/
theorem core_equality (R : Matrix ι κ ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℕ)
    (hl : Fintype.card ι = 16) (hb : Fintype.card κ = 11)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hrow : ∀ i, (∑ j, E i j) + (δ i : ℝ) = 3) (htotal : ∑ i, δ i = 18)
    (hgram : R * R.transpose = Matrix.diagonal (fun _ => (3 : ℝ)) + E +
      Matrix.of (fun _ _ => (3 : ℝ))) :
    (univ.filter (fun i => δ i = 0)).card = 10 ∧
    (∀ i, δ i = 0 ∨ δ i = 3) ∧
    (∀ i, δ i = 3 → ∀ j, E i j = 0) ∧
    finrank ℝ (LinearMap.ker (Matrix.diagonal (fun _ => (3 : ℝ)) + E).mulVecLin) = 5 ∧
    LinearMap.ker (R * R.transpose).mulVecLin =
      LinearMap.ker (Matrix.diagonal (fun _ => (3 : ℝ)) + E).mulVecLin ∧
    R.rank = 11 := by
  classical
  let Z := univ.filter (fun i => δ i = 0)
  have hδle (i : ι) : δ i ≤ 3 := by
    have hh := hrow i
    have hsum : 0 ≤ ∑ j, E i j := sum_nonneg fun j _ => hn i j
    have hd : (δ i : ℝ) ≤ 3 := by linarith
    exact_mod_cast hd
  have hcap (i : ι) : δ i + (if δ i = 0 then 3 else 0) ≤ 3 := by
    split_ifs with hi <;> simp_all
  have hsum : (∑ i, (δ i + if δ i = 0 then 3 else 0)) = 18 + 3*Z.card := by
    rw [sum_add_distrib,htotal,← sum_filter]
    simp [Z,Nat.mul_comm]
  have hbound := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hcap i)
  rw [hsum] at hbound
  simp only [sum_const,card_univ,Nat.nsmul_eq_mul,hl] at hbound
  have hP := TwoKMinusTwoEquality.constant_posSemidef (ι := ι) 3 (by norm_num)
  have hg := BoundaryRank.gram_card_bound R 3 E (fun i => (δ i : ℝ)) (by norm_num)
    hs hn hz (fun i => Nat.cast_nonneg _) hrow _ hP hgram
  simp only [hl,hb,Nat.cast_eq_zero] at hg
  change 2*16 ≤ 2*11 + Z.card at hg
  have hZ : Z.card = 10 := by omega
  have hall (i : ι) : δ i + (if δ i = 0 then 3 else 0) = 3 := by
    apply le_antisymm (hcap i)
    by_contra hi
    have hi' : δ i + (if δ i = 0 then 3 else 0) < 3 := by omega
    have hlt := sum_lt_sum (fun j (_ : j ∈ (univ : Finset ι)) => hcap j)
      ⟨i,mem_univ _,hi'⟩
    rw [hsum,hZ] at hlt
    simp [hl] at hlt
  have hd (i : ι) : δ i = 0 ∨ δ i = 3 := by
    have hh := hall i
    by_cases hi : δ i = 0
    · exact Or.inl hi
    · simp only [if_neg hi,add_zero] at hh
      exact Or.inr hh
  have hiso (i : ι) (hi : δ i = 3) (j : ι) : E i j = 0 := by
    have hr := hrow i
    rw [hi] at hr
    have hij := single_le_sum (f := E i) (fun k _ => hn i k) (mem_univ j)
    have hnon := hn i j
    norm_num at hr
    linarith
  have hpsd := BoundaryRank.signless_posSemidef (fun _ => (3 : ℝ))
    (fun i => (δ i : ℝ)) E hs hn (fun _ => Nat.cast_nonneg _) hrow
  have hker := BoundaryRank.ker_add_le_of_posSemidef hpsd hP
  rw [← hgram] at hker
  have hdim := Submodule.finrank_mono hker
  have hnull := BoundaryRank.two_mul_nullity_le_zero_count 3 E (fun i => (δ i : ℝ))
    (by norm_num) hs hn hz (fun _ => Nat.cast_nonneg _) hrow
  simp only [Nat.cast_eq_zero] at hnull
  change 2 * _ ≤ Z.card at hnull
  rw [hZ] at hnull
  have hrank : (R * R.transpose).rank ≤ 11 := by
    exact (Matrix.rank_mul_le_left R R.transpose).trans (by simpa [hb] using R.rank_le_card_width)
  have htotalrank : (R * R.transpose).rank +
      finrank ℝ (LinearMap.ker (R * R.transpose).mulVecLin) = 16 := by
    simpa [Matrix.rank,hl] using LinearMap.finrank_range_add_finrank_ker (R * R.transpose).mulVecLin
  have hA : finrank ℝ (LinearMap.ker (Matrix.diagonal (fun _ => (3 : ℝ)) + E).mulVecLin) = 5 := by omega
  have hB : finrank ℝ (LinearMap.ker (R * R.transpose).mulVecLin) = 5 := by omega
  have hkeq : LinearMap.ker (R * R.transpose).mulVecLin =
      LinearMap.ker (Matrix.diagonal (fun _ => (3 : ℝ)) + E).mulVecLin := by
    exact Submodule.eq_of_le_of_finrank_eq hker (hB.trans hA.symm)
  have hR : R.rank = 11 := by
    have hu := R.rank_le_card_width
    have hh := Matrix.rank_mul_le_left R R.transpose
    rw [hb] at hu
    omega
  exact ⟨hZ,hd,hiso,hA,hkeq,hR⟩

/-- Five paired zero-deficit components and six isolated deficit-three rows.
Equal incidence rows are deduced using the specific constant remainder 3J. -/
theorem core_pairing (R : Matrix ι κ ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℕ)
    (hl : Fintype.card ι = 16) (hb : Fintype.card κ = 11)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hrow : ∀ i, (∑ j, E i j) + (δ i : ℝ) = 3) (htotal : ∑ i, δ i = 18)
    (hgram : R * R.transpose = Matrix.diagonal (fun _ => (3 : ℝ)) + E +
      Matrix.of (fun _ _ => (3 : ℝ))) :
    ∃ e : ((Fin 5 × Bool) ⊕ Fin 6) ≃ ι,
      (∀ i b, δ (e (.inl (i,b))) = 0) ∧
      (∀ i, δ (e (.inr i)) = 3) ∧
      (∀ i j, i ≠ j → ∀ b c, E (e (.inl (i,b))) (e (.inl (j,c))) = 0) ∧
      (∀ i, E (e (.inl (i,false))) (e (.inl (i,true))) = 3) ∧
      (∀ i j, E (e (.inr i)) j = 0) ∧
      (∀ i j, R (e (.inl (i,false))) j = R (e (.inl (i,true))) j) := by
  classical
  obtain ⟨hZ,hd,hiso,hA,_,_⟩ := core_equality R E δ hl hb hs hn hz hrow htotal hgram
  let Z := univ.filter (fun i => (δ i : ℝ) = 0)
  have hc : ∀ i j, (δ i : ℝ) = 0 → (δ j : ℝ) ≠ 0 → E i j = 0 := by
    intro i j _ hj
    have hj' : δ j ≠ 0 := by exact_mod_cast hj
    rw [hs]
    exact hiso j ((hd j).resolve_left hj') i
  have hpair := BoundaryRank.restricted_kernel_pairing (κ := Fin 5) 3 E (fun i => (δ i : ℝ))
    (by norm_num) hs hn hz (fun _ => Nat.cast_nonneg _) hrow hc
    (by simpa using hZ) (by simp [hA])
  obtain ⟨eZ,hcross,hweight⟩ := hpair
  have hW : Fintype.card {i : ι // i ∉ Z} = 6 := by
    have hzc : Fintype.card {i : ι // i ∈ Z} = 10 := by
      rw [Fintype.card_coe]
      simpa [Z] using hZ
    rw [Fintype.card_subtype_compl,hl,hzc]
  let eW : Fin 6 ≃ {i : ι // i ∉ Z} := (Fintype.equivFinOfCardEq hW).symm
  let e : ((Fin 5 × Bool) ⊕ Fin 6) ≃ ι :=
    (Equiv.sumCongr eZ eW).trans (Equiv.sumCompl (fun i => i ∈ Z))
  have h0 (i : Fin 5) (b : Bool) : δ (e (.inl (i,b))) = 0 :=
    by exact_mod_cast (mem_filter.mp (eZ (i,b)).property).2
  have h3 (i : Fin 6) : δ (e (.inr i)) = 3 := by
    apply (hd _).resolve_left
    change δ (eW i).val ≠ 0
    have hh := (eW i).property
    simpa [Z] using hh
  have hcross' : ∀ i j, i ≠ j → ∀ b c,
      E (e (.inl (i,b))) (e (.inl (j,c))) = 0 := hcross
  have hweight' : ∀ i, E (e (.inl (i,false))) (e (.inl (i,true))) = 3 := hweight
  refine ⟨e,h0,h3,hcross',hweight',fun i => hiso _ (h3 i),?_⟩
  intro i j
  have hself (x : ι) : (R * R.transpose) x x = 6 := by rw [hgram]; norm_num [hz]
  have hne : e (.inl (i,false)) ≠ e (.inl (i,true)) := by
    intro he
    have hh := e.injective he
    cases hh
  apply TwoKMinusTwoEquality.rows_eq_of_gram R _ _ 6 (hself _) (hself _) _ j
  rw [hgram]
  norm_num [hne,hweight']

end CoveringDesigns.C18_10_3
