import CoveringDesigns.BoundaryRank.Capacity

/-!
# Fourteen occurrences in a threefold pair cover

All point and occurrence types are arbitrary finite types. Repeated blocks
are permitted. The proof counts occurrences throughout and derives the
degree floor. Budgets below thirteen are excluded directly by the same
incidence/rank inequalities, so no padding or deduplication is needed.
-/
namespace CoveringDesigns.TwoKMinusTwoCapacity
open Finset Matrix BoundaryRank BoundaryIncidence
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] {k : ℕ}

/-- Pair counting alone gives the degree-six floor; no triple coverage. -/
theorem indexed_degree_ge_six (B : ι → Finset α)
    (hv : Fintype.card α = 2*k-2) (hk : 5 ≤ k)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ indexedSubsetDegree B {x,y}) (x : α) :
    6 ≤ indexedDegree B x := by
  classical
  have hp (y : α) :
      3 + (if x=y then indexedDegree B x else 0) ≤
        indexedSubsetDegree B {x,y} + (if x=y then 3 else 0) := by
    by_cases he : x=y
    · subst y
      simp [Nat.add_comm]
    · simpa [he] using hpair x y he
  have hs := sum_le_sum (s := (univ : Finset α)) (fun y _ => hp y)
  simp only [sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul,
    sum_ite_eq, mem_univ, ite_true, indexed_pair_sum_of_uniform B hsize x] at hs
  have hv' : Fintype.card α + 2 = 2*k := by omega
  by_contra hn
  have hd : indexedDegree B x ≤ 5 := by omega
  have hm := Nat.mul_le_mul_left (k-1) hd
  have hkm : k-1+1=k := by omega
  nlinarith

private theorem boundary_six (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) :
    (6 : ℝ)*((k : ℝ)-1)-3*((Fintype.card α : ℝ)-1)=6-3 := by
  have hh : Fintype.card α + 2 = 2*k := by omega
  have hR : (Fintype.card α : ℝ)+2=2*(k : ℝ) := by exact_mod_cast hh
  linarith

/-- Reconstructed thirteen-occurrence counts, retaining integer excess η
and the actual rank. The lower count is stated without subtraction. -/
theorem thirteen_budget (B : ι → Finset α)
    (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ indexedSubsetDegree B {x,y})
    (hb : Fintype.card ι = 13) :
    (lowPoints B 6).card = k-14+eta B 6 ∧
    positiveCount B 6 3 + 2*(13-(incidence B 6).rank) + eta B 6 + k ≤ 40 ∧
    1 ≤ 13-(incidence B 6).rank ∧
    4*k+6*(13-(incidence B 6).rank)+eta B 6 ≤ (regularPoints B 6 3).card+108 := by
  have hdeg := indexed_degree_ge_six B hv (by omega) hsize hpair
  have hbound := boundary_six hv (by omega)
  have hcenter : (6 : ℝ)^2 ≤ (Fintype.card ι : ℝ)*3 := by rw [hb]; norm_num
  obtain ⟨_, _, hu, hr⟩ := completion B (by omega) (by norm_num : 3<6)
    hsize hpair hbound hcenter
  have hd := degree_balance B hsize hdeg
  have hw := (incidence B 6).rank_le_card_width
  have hl := lowerCount_le B (by omega) (by norm_num : 3<6)
    hsize hdeg hpair hbound hcenter
  have hv' : Fintype.card α + 2 = 2*k := by omega
  have hvR : (Fintype.card α : ℝ) = 2*(k : ℝ)-2 := by
    have hh : (Fintype.card α : ℝ)+2=2*(k : ℝ) := by exact_mod_cast hv'
    linarith
  rw [hb] at hd hu hw hl
  norm_num only [Nat.reduceAdd] at hd
  have he : (lowPoints B 6).card = k-14+eta B 6 := by omega
  refine ⟨he, by omega, hu, ?_⟩
  unfold lowerCount at hl
  rw [hvR] at hl
  norm_num at hl
  have hLR : (4 : ℝ)*k+6*(13-(incidence B 6).rank : ℕ)+eta B 6 ≤
      (regularPoints B 6 3).card+108 := by nlinarith [hl]
  exact_mod_cast hLR

/-- Thirteen occurrences contradict support count times clone capacity
throughout k≥33, using a symbolic corank split. -/
theorem no_thirteen (B : ι → Finset α)
    (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ indexedSubsetDegree B {x,y})
    (hb : Fintype.card ι = 13) : False := by
  obtain ⟨_, hbudget, hu, hlow⟩ := thirteen_budget B hv hk hsize hpair hb
  have hbound := boundary_six hv (by omega)
  have hv' : Fintype.card α + 2 = 2*k := by omega
  have hvR : (Fintype.card α : ℝ) = 2*(k : ℝ)-2 := by
    have hh : (Fintype.card α : ℝ)+2=2*(k : ℝ) := by exact_mod_cast hv'
    linarith
  have hA : 0 ≤ ((6 : ℝ)+1)*k-3*Fintype.card α := by
    rw [hvR]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hcap := clone_bound B (by omega) (by norm_num : 3<6)
    hsize hpair hbound (by rw [hb]; norm_num) hA
  rw [hb, hvR] at hcap
  have hlowR : (4 : ℝ)*k + 6*(13-(incidence B 6).rank : ℕ) + eta B 6 ≤
      (regularPoints B 6 3).card+108 := by exact_mod_cast hlow
  have hkR : (33 : ℝ) ≤ k := by exact_mod_cast hk
  have hη : (0 : ℝ) ≤ eta B 6 := Nat.cast_nonneg _
  have hu3 : 13-(incidence B 6).rank ≤ 3 := by omega
  have hcases : 13-(incidence B 6).rank = 1 ∨
      13-(incidence B 6).rank = 2 ∨ 13-(incidence B 6).rank = 3 := by omega
  rcases hcases with he | he | he
  · rw [he] at hlowR hcap
    norm_num at hlowR hcap
    -- The necessary scalar inequality has positive gap 15*k - 414.
    nlinarith
  · rw [he] at hlowR hcap
    norm_num at hlowR hcap
    -- The positive gap is 14*k - 396.
    nlinarith
  · rw [he] at hlowR hcap
    norm_num at hlowR hcap
    -- The positive gap is 12*k - 384.
    nlinarith

/-- Every indexed threefold pair cover needs fourteen occurrences.
No injectivity, triple coverage, degree floor or small-budget premise. -/
theorem indexed_fourteen_le_card (B : ι → Finset α)
    (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ indexedSubsetDegree B {x,y}) :
    14 ≤ Fintype.card ι := by
  have hdeg := indexed_degree_ge_six B hv (by omega) hsize hpair
  have hsum := sum_le_sum (s := (univ : Finset α)) (fun x _ => hdeg x)
  simp only [sum_const, card_univ, Nat.nsmul_eq_mul,
    BoundaryIncidence.degree_sum B hsize] at hsum
  have hv' : Fintype.card α + 2 = 2*k := by omega
  have hb12 : 12 ≤ Fintype.card ι := by
    by_contra hn
    have hb11 : Fintype.card ι ≤ 11 := by omega
    have hm := Nat.mul_le_mul_left k hb11
    nlinarith
  by_contra hn
  have hb13 : Fintype.card ι ≤ 13 := by omega
  by_cases he : Fintype.card ι = 13
  · exact no_thirteen B hv hk hsize hpair he
  have he12 : Fintype.card ι = 12 := by omega
  have hbound := boundary_six hv (by omega)
  obtain ⟨_, _, _, hr⟩ := completion B (by omega) (by norm_num : 3<6)
    hsize hpair hbound (by rw [he12]; norm_num)
  have hd := degree_balance B hsize hdeg
  have hw := (incidence B 6).rank_le_card_width
  rw [he12] at hd hw
  norm_num only [Nat.reduceAdd] at hd
  omega

end CoveringDesigns.TwoKMinusTwoCapacity
