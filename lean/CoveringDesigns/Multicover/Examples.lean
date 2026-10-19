import CoveringDesigns.Multicover.Family
import CoveringDesigns.Multicover.Multiset

/-! Structural boundary checks and two fixed multiplicity-two calibrations. -/

namespace CoveringDesigns.Multicover.Examples

open Finset
universe u v
variable {α : Type u} [DecidableEq α]

theorem empty_occurrences (k t : ℕ) :
    IsCover (fun i : Fin 0 => (Fin.elim0 i : Finset α)) k t 0 :=
  ⟨fun i => Fin.elim0 i, covers_multiplicity_zero _ _⟩

theorem repeated_empty (lam : ℕ) :
    IsCover (fun _ : Fin lam => (∅ : Finset α)) 0 0 lam := by
  refine ⟨fun _ => rfl, (covers_zero_iff _ _).mpr ?_⟩
  simp

theorem empty_points (lam : ℕ) :
    IsCover (fun _ : Fin lam => (∅ : Finset PEmpty)) 0 0 lam := repeated_empty lam

theorem full_copies [Fintype α] (lam t : ℕ) :
    IsCover (fun _ : Fin lam => (univ : Finset α)) (Fintype.card α) t lam := by
  refine ⟨fun _ => card_univ, ?_⟩
  intro X _
  simp [indexedSubsetDegree]

theorem full_copies_link [Fintype α] (lam : ℕ) (X : Finset α) :
    Fintype.card {_i : Fin lam // X ⊆ (univ : Finset α)} = lam ∧
      ∀ i, subsetLink (fun _ : Fin lam => (univ : Finset α)) X i = univ := by
  constructor
  · simp
  · intro i
    ext p
    simp [subsetLink]

theorem empty_subset_link {ι : Type v} [Fintype ι]
    {B : ι → Finset α} {k t lam : ℕ} (h : IsCover B k t lam) :
    Fintype.card {i // (∅ : Finset α) ⊆ B i} = Fintype.card ι ∧
      IsCover (subsetLink B ∅) k t lam := by
  constructor
  · rw [subsetLink_card, subsetDegree_empty]
  · simpa using subsetLink_isCover h ∅ (by simp)

theorem strength_zero_link {ι : Type v} [Fintype ι]
    {B : ι → Finset α} {k t lam : ℕ} (h : IsCover B k t lam)
    {X : Finset α} (hX : X.card = t) :
    IsCover (subsetLink B X) (k-t) 0 lam ∧ lam ≤ indexedSubsetDegree B X := by
  exact ⟨by simpa only [hX, Nat.sub_self] using subsetLink_isCover h X (by omega),
    h.2 X hX⟩

/-- Forgetting repeats can destroy multiplicity-two coverage even at strength zero. -/
theorem deduplication_loses_multiplicity :
    IsCover (fun _ : Fin 2 => (∅ : Finset PEmpty)) 0 0 2 ∧
      ¬ Covers (ofFamily (deduplicate (fun _ : Fin 2 => (∅ : Finset PEmpty)))) 0 2 := by
  refine ⟨repeated_empty 2, ?_⟩
  simp [covers_zero_iff, deduplicate]

theorem repeated_multiset (lam : ℕ) :
    Fintype.card (Multiset.replicate lam (∅ : Finset α)) = lam ∧
      IsCover (ofMultiset (Multiset.replicate lam (∅ : Finset α))) 0 0 lam := by
  refine ⟨by simp, ?_, (covers_zero_iff _ _).mpr (by simp)⟩
  apply (ofMultiset_uniform _ _).mpr
  intro A hA
  rw [Multiset.eq_of_mem_replicate hA]
  rfl

theorem numerical_values : bound 2 4 3 2 = 4 ∧ bound 2 5 3 2 = 7 := by decide

theorem lower_bound_4_3_2 [Fintype α] {ι : Type v} [Fintype ι]
    {B : ι → Finset α} (hn : Fintype.card α = 4) (h : IsCover B 3 2 2) :
    4 ≤ Fintype.card ι := by
  have hb := lower_bound (by decide : 2 ≤ 3) (by omega) h
  simpa only [hn, numerical_values.1] using hb

theorem lower_bound_5_3_2 [Fintype α] {ι : Type v} [Fintype ι]
    {B : ι → Finset α} (hn : Fintype.card α = 5) (h : IsCover B 3 2 2) :
    7 ≤ Fintype.card ι := by
  have hb := lower_bound (by decide : 2 ≤ 3) (by omega) h
  simpa only [hn, numerical_values.2] using hb

end CoveringDesigns.Multicover.Examples
