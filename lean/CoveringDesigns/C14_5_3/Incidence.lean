import CoveringDesigns.ExactDesign.Counting
import CoveringDesigns.LabelledCliques.Extensions
import Mathlib.Tactic.NormNum

/-! Finite trace counts for occurrence-indexed families. The incidence and
link representations are the existing library definitions.
Formalisation: Rob Gardiner, with AI assistance. -/

namespace CoveringDesigns.C14_5_3
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

theorem multiplicity_one_iff (B : ι → Finset α) (T : Finset α) :
    indexedSubsetDegree B T = 1 ↔ ∃! i, T ⊆ B i := by
  classical
  simp only [indexedSubsetDegree, card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    have hm : ∀ j, T ⊆ B j ↔ j = i := by
      intro j
      have := congrArg (fun s : Finset ι => j ∈ s) hi
      simpa using this
    exact ⟨i, (hm i).mpr rfl, fun j hj => (hm j).mp hj⟩
  · rintro ⟨i, hi, hu⟩
    refine ⟨i, ?_⟩
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨hu j, fun h => h ▸ hi⟩

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

theorem restrict_add_complement (B : ι → Finset α) (p : ι → Prop)
    [DecidablePred p] [Fintype {i // p i}] [Fintype {i // ¬ p i}] (T : Finset α) :
    indexedSubsetDegree (fun i : {i // p i} => B i) T +
      indexedSubsetDegree (fun i : {i // ¬ p i} => B i) T =
        indexedSubsetDegree B T := by
  classical
  rw [restrict_multiplicity, restrict_multiplicity]
  have hf : ∀ q : ι → Prop, [DecidablePred q] →
      univ.filter (fun i => q i ∧ T ⊆ B i) =
        (univ.filter (fun i => T ⊆ B i)).filter q := by
    intro q _
    ext i
    simp [and_comm]
  rw [hf p, hf (fun i => ¬ p i)]
  exact card_filter_add_card_filter_not _

end CoveringDesigns.C14_5_3
