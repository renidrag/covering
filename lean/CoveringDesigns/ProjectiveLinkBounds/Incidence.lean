import CoveringDesigns.ExactDesign.Counting
import CoveringDesigns.ProjectiveLinkBounds.Arithmetic
import Mathlib.Tactic.NormNum

/-! Local trace and restriction counts for projective links. The incidence and
link representations are the existing library definitions.
Formalisation: Rob Gardiner, with AI assistance. -/

namespace CoveringDesigns.ProjectiveLinkBounds.Internal
open Finset
universe u v
variable {α : Type u} {ι : Type v} [DecidableEq α] [Fintype ι]

theorem multiplicity_mono (B : ι → Finset α) {S T : Finset α} (h : S ⊆ T) :
    indexedSubsetDegree B T ≤ indexedSubsetDegree B S := by
  apply card_le_card
  exact fun i hi => mem_filter.mpr ⟨mem_univ i, h.trans (mem_filter.mp hi).2⟩

theorem multiplicity_pos_iff (B : ι → Finset α) (T : Finset α) :
    0 < indexedSubsetDegree B T ↔ ∃ i, T ⊆ B i := by
  simp [indexedSubsetDegree, card_pos, Finset.nonempty_def]

theorem multiplicity_ge_two (B : ι → Finset α) {T : Finset α}
    {i j : ι} (hij : i ≠ j) (hi : T ⊆ B i) (hj : T ⊆ B j) :
    2 ≤ indexedSubsetDegree B T := by
  classical
  have h : ({i, j} : Finset ι) ⊆ univ.filter (fun i => T ⊆ B i) := by
    intro k hk
    rcases mem_insert.mp hk with rfl | hk
    · simp [hi]
    · have := mem_singleton.mp hk
      subst k
      simp [hj]
  simpa [indexedSubsetDegree, hij] using card_le_card h

/-- Restricted subset incidence: repetitions are counted at their indices. -/
theorem trace_count (B : ι → Finset α) (S : Finset α) (r : ℕ) :
    (∑ T ∈ S.powersetCard r, indexedSubsetDegree B T) =
      ∑ i, ((B i ∩ S).card).choose r := by
  classical
  simp only [indexedSubsetDegree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [sum_const, Nat.nsmul_eq_mul, mul_one]
  rw [← sum_filter, ← card_eq_sum_ones, ← card_powersetCard]
  congr 1
  ext T
  simp only [mem_filter, mem_powersetCard, subset_inter_iff]
  tauto

theorem intersection_sum (B : ι → Finset α) (S : Finset α) :
    (∑ i, (B i ∩ S).card) = ∑ x ∈ S, indexedDegree B x := by
  classical
  simp only [indexedDegree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter]
  congr 1
  ext x
  simp [and_comm]

/-- Count any selected set of subsets against the actual containing indices. -/
theorem selected_subset_count (B : ι → Finset α) (A : Finset (Finset α)) :
    (∑ T ∈ A, indexedSubsetDegree B T) =
      ∑ i, (A.filter (· ⊆ B i)).card := by
  classical
  simp only [indexedSubsetDegree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]

/-- Passing to a subtype removes exactly the excluded indices, not their images. -/
theorem restrict_multiplicity (B : ι → Finset α) (p : ι → Prop) [DecidablePred p]
    [Fintype {i // p i}]
    (T : Finset α) :
    indexedSubsetDegree (fun i : {i // p i} => B i) T =
      (univ.filter (fun i => p i ∧ T ⊆ B i)).card := by
  classical
  unfold indexedSubsetDegree
  have he : (univ.filter (fun i : {i // p i} => T ⊆ B i)) =
      (univ.filter (fun i => T ⊆ B i)).subtype p := by
    ext i
    simp
  rw [he, card_subtype]
  congr 1
  ext i
  simp [and_comm]

theorem degree_through_point (B : ι → Finset α) (p x : α) :
    indexedDegree (fun i : {i // p ∈ B i} => B i) x =
      indexedSubsetDegree B {p,x} := by
  classical
  rw [← Multicover.subsetDegree_singleton, restrict_multiplicity]
  unfold indexedSubsetDegree
  congr 1
  ext i
  simp [insert_subset_iff, singleton_subset_iff]

variable [Fintype α]

private theorem pair_row {B : ι → Finset α} {q : ℕ}
    (hu : Multicover.Uniform B (q+1)) (x : α) :
    (∑ y ∈ univ.erase x, indexedSubsetDegree B {x,y}) = q * indexedDegree B x := by
  classical
  let D := fun i : {i // x ∈ B i} => B i.val
  have hs := intersection_sum D (univ.erase x)
  have he (i : {i // x ∈ B i}) : (D i ∩ univ.erase x).card = q := by
    have hh : D i ∩ univ.erase x = (B i.val).erase x := by ext y; simp [D, and_comm]
    rw [hh, card_erase_of_mem i.property, hu i.val]
    omega
  have hc : Fintype.card {i // x ∈ B i} = indexedDegree B x := by
    simp [Fintype.card_subtype, indexedDegree]
  simpa only [D, degree_through_point, he, sum_const, card_univ,
    Nat.nsmul_eq_mul, hc, Nat.mul_comm] using hs.symm

theorem pair_point_floor {B : ι → Finset α} {q : ℕ} (hq : 1 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (x : α) : q+1 ≤ indexedDegree B x := by
  classical
  have hs := sum_le_sum (s := (univ : Finset α).erase x)
    (fun y hy => hB.2 {x,y} (by simp [Ne.symm (mem_erase.mp hy).1]))
  rw [pair_row hB.1 x] at hs
  simp only [sum_const, Nat.nsmul_eq_mul, mul_one, card_erase_of_mem (mem_univ x),
    card_univ, hv, pointCount] at hs
  have he : q^2+q+1-1=q^2+q := by omega
  rw [he] at hs
  nlinarith

theorem regular_pair {B : ι → Finset α} {q : ℕ}
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    {x y : α} (hx : indexedDegree B x = q+1) (hxy : x ≠ y) :
    indexedSubsetDegree B {x,y} = 1 := by
  classical
  have hl (y : α) (hy : y ∈ (univ : Finset α).erase x) :
      1 ≤ indexedSubsetDegree B {x,y} :=
    hB.2 _ (by simp [Ne.symm (mem_erase.mp hy).1])
  have he : (∑ y ∈ (univ : Finset α).erase x, 1) =
      ∑ y ∈ (univ : Finset α).erase x, indexedSubsetDegree B {x,y} := by
    rw [pair_row hB.1 x, hx]
    simp [card_erase_of_mem, hv, pointCount]
    ring
  exact ((sum_eq_sum_iff_of_le hl).mp he y (by simp [Ne.symm hxy])).symm

theorem pair_cover_lower {B : ι → Finset α} {q : ℕ} (hq : 1 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1) :
    pointCount q ≤ Fintype.card ι := by
  have hs := sum_le_sum (s := (univ : Finset α))
    (fun x _ => pair_point_floor hq hv hB x)
  rw [Multicover.degree_sum_of_uniform hB.1] at hs
  simp only [sum_const, card_univ, hv, Nat.nsmul_eq_mul] at hs
  nlinarith

theorem pair_cover_exact {B : ι → Finset α} {q : ℕ} (hq : 1 ≤ q)
    (hv : Fintype.card α = pointCount q) (hB : Multicover.IsCover B (q+1) 2 1)
    (hn : Fintype.card ι = pointCount q) : ExactDesign.IsDesign B (q+1) 2 1 := by
  have hl (x : α) (_ : x ∈ (univ : Finset α)) : q+1 ≤ indexedDegree B x :=
    pair_point_floor hq hv hB x
  have he : (∑ _x : α, (q+1)) = ∑ x, indexedDegree B x := by
    rw [Multicover.degree_sum_of_uniform hB.1]
    simp [hv, hn, Nat.mul_comm]
  have hd (x : α) : indexedDegree B x = q+1 :=
    ((sum_eq_sum_iff_of_le hl).mp he x (mem_univ x)).symm
  refine ⟨hB.1, ?_⟩
  intro P hP
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hP
  exact regular_pair hv hB (hd x) hxy

theorem exact_point_count {L : ι → Finset α} {q : ℕ} (hq : 1 ≤ q)
    (hv : Fintype.card α = pointCount q) (hL : ExactDesign.IsDesign L (q+1) 2 1)
    (x : α) : indexedDegree L x = q+1 := by
  have h := hL.residual_count (i := 1) (by omega) (X := {x}) (by simp)
  simp only [hv, pointCount, Nat.add_sub_cancel, Nat.choose_one_right,
    Nat.reduceSub, one_mul, Multicover.subsetDegree_singleton] at h
  nlinarith

theorem exact_line_count {L : ι → Finset α} {q : ℕ} (hq : 1 ≤ q)
    (hv : Fintype.card α = pointCount q) (hL : ExactDesign.IsDesign L (q+1) 2 1) :
    Fintype.card ι = pointCount q := by
  have hs := Multicover.degree_sum_of_uniform hL.1
  simp only [exact_point_count hq hv hL, sum_const, card_univ, Nat.nsmul_eq_mul, hv] at hs
  nlinarith

omit [Fintype α] in
theorem exact_multiplicity_le_one {L : ι → Finset α} {q : ℕ}
    (hL : ExactDesign.IsDesign L (q+1) 2 1) {T : Finset α} (hT : 2 ≤ T.card) :
    indexedSubsetDegree L T ≤ 1 := by
  obtain ⟨P,hP,hc⟩ := exists_subset_card_eq hT
  exact (multiplicity_mono L hP).trans (hL.2 P hc).le

omit [Fintype α] in
theorem exact_line_intersection {L : ι → Finset α} {q : ℕ}
    (hL : ExactDesign.IsDesign L (q+1) 2 1) {i j : ι} (hij : i ≠ j) :
    (L i ∩ L j).card ≤ 1 := by
  by_contra h
  obtain ⟨P,hP,hc⟩ := exists_subset_card_eq (show 2 ≤ (L i ∩ L j).card by omega)
  have hh := multiplicity_ge_two L hij (hP.trans inter_subset_left)
    (hP.trans inter_subset_right)
  rw [hL.2 P hc] at hh
  omega

end CoveringDesigns.ProjectiveLinkBounds.Internal

