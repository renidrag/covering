import CoveringDesigns.PairEquality.Classification
import CoveringDesigns.TruncatedPlaneLoads.Actual
import CoveringDesigns.Multicover.Family

/-! From actual indexed pair coverings to the unchanged geometric interface.
Repeated occurrences and distinct points with identical supports are allowed. -/
namespace CoveringDesigns.PairDivisibility
open Finset TruncatedPlaneLoads
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
variable {q k : ℕ} {B : I → Finset X}

/-- The elementary point-degree floor, without a supplied geometric core. -/
theorem degree_floor (hq : 2 ≤ q) (hk : 0 < k) (hv : Fintype.card X = q*k)
    (hB : Multicover.IsCover B k 2 1) (p : X) : q+1 ≤ (support B p).card := by
  have sub : univ.erase p ⊆ (support B p).biUnion (fun i => (B i).erase p) := by
    intro r hr
    have hpr : p ≠ r := Ne.symm (mem_erase.mp hr).1
    obtain ⟨i,hi⟩ := (Multicover.covers_one_iff _ _).mp hB.2 {p,r} (by simp [hpr])
    simp only [insert_subset_iff,singleton_subset_iff] at hi
    exact mem_biUnion.mpr ⟨i,by simp [hi.1],mem_erase.mpr ⟨hpr.symm,hi.2⟩⟩
  have cap := (card_le_card sub).trans (card_biUnion_le)
  have sizes : (∑ i ∈ support B p, ((B i).erase p).card) = (support B p).card*(k-1) := by
    calc
      _ = ∑ _i ∈ support B p, (k-1) := by
        apply sum_congr rfl
        intro i hi
        rw [card_erase_of_mem ((mem_support B p i).mp hi), hB.1 i]
      _ = _ := by simp
  rw [sizes, card_erase_of_mem (mem_univ p), card_univ, hv] at cap
  by_contra hn
  have hd : (support B p).card ≤ q := by omega
  have hc := Nat.mul_le_mul_right (k-1) hd
  have hp : 0 < q*k := Nat.mul_pos (by omega) hk
  have hsub : k-1+1 = k := by omega
  have hsub' : q*k-1+1 = q*k := by omega
  nlinarith

private theorem degree_sum (hB : Multicover.Uniform B k) :
    (∑ p : X, (support B p).card) = k * Fintype.card I := by
  simp only [support,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  have hh (i : I) : (∑ p : X, if p ∈ B i then 1 else 0) = k := by
    rw [← sum_filter]
    simpa using hB i
  simp [hh,Nat.mul_comm]

/-- At least q(q+1) block occurrences, even if block images repeat. -/
theorem incidence_floor (hq : 4 ≤ q) (hk : q ≤ k) (hv : Fintype.card X = q*k)
    (hB : Multicover.IsCover B k 2 1) : q*(q+1) ≤ Fintype.card I := by
  have hf := sum_le_sum (fun p (_ : p ∈ (univ : Finset X)) =>
    degree_floor (by omega) (by omega) hv hB p)
  rw [degree_sum hB.1] at hf
  simp only [sum_const,card_univ,nsmul_eq_mul,hv] at hf
  nlinarith

theorem equality_support_size (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hi : Fintype.card I = q*(q+1))
    (hB : Multicover.IsCover B k 2 1) (p : X) : (support B p).card = q+1 := by
  have floors := degree_floor (by omega : 2 ≤ q) (by omega : 0 < k) hv hB
  have eq : (∑ _p : X, (q+1)) = ∑ p : X, (support B p).card := by
    rw [degree_sum hB.1]
    simp [hv,hi]
    ring
  exact ((sum_eq_sum_iff_of_le (fun x _ => floors x)).mp eq p (mem_univ _)).symm

/-- Normalization retains the original coordinate type and actual support subsets.
Only multiplicities are divided by the positive block size. -/
theorem normalized_loads (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hi : Fintype.card I = q*(q+1))
    (hB : Multicover.IsCover B k 2 1) :
    PairEquality.PositiveUnitLoads q (occupied B) (fun E => (multiplicity B E : ℝ)/k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine ⟨hi,?_,?_,?_,?_⟩
  · intro E hE
    obtain ⟨p,_,rfl⟩ := mem_image.mp hE
    exact equality_support_size hq hk hv hi hB p
  · intro E hE F hF hEF
    obtain ⟨p,_,rfl⟩ := mem_image.mp hE
    obtain ⟨r,_,rfl⟩ := mem_image.mp hF
    have hpr : p ≠ r := by intro he; subst r; exact hEF rfl
    obtain ⟨i,hi⟩ := (Multicover.covers_one_iff _ _).mp hB.2 {p,r} (by simp [hpr])
    exact ⟨i,by simpa only [mem_inter,mem_support,insert_subset_iff,singleton_subset_iff] using hi⟩
  · intro E hE
    exact div_pos (by exact_mod_cast multiplicity_pos B hE) hk0
  · intro x
    have he : (∑ E ∈ occupied B, if x ∈ E then (multiplicity B E : ℝ) else 0) = k := by
      exact_mod_cast (actual_load B x).trans (hB.1 x)
    calc
      _ = (∑ E ∈ occupied B, if x ∈ E then (multiplicity B E : ℝ) else 0) / k := by
        simp only [div_eq_mul_inv,sum_mul]
        apply sum_congr rfl
        intro E hE
        split_ifs <;> simp
      _ = 1 := by rw [he,div_self (ne_of_gt hk0)]

end CoveringDesigns.PairDivisibility
