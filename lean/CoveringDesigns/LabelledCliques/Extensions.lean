import CoveringDesigns.Multicover.Counting
import Mathlib.Tactic.Linarith

/-! Immediate-extension counting through occurrence-preserving links.
No new incidence double count and no deduplication are used. -/
namespace CoveringDesigns.LabelledCliques
open Finset
universe u w
variable {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι]

/-- The subsets one point larger than `S` that contain `S`. -/
def extensions (S : Finset α) : Finset (Finset α) :=
  (univ.powersetCard (S.card+1)).filter (S ⊆ ·)

@[simp] theorem mem_extensions {S T : Finset α} :
    T ∈ extensions S ↔ S ⊆ T ∧ T.card = S.card+1 := by
  simp [extensions, and_comm]

theorem extension_eq_insert {S T : Finset α} (h : T ∈ extensions S) :
    ∃ x, x ∉ S ∧ insert x S = T := by
  have h' := mem_extensions.mp h
  have hc : (T \ S).card = 1 := by
    rw [card_sdiff_of_subset h'.1, h'.2]; omega
  obtain ⟨x, hx⟩ := card_eq_one.mp hc
  refine ⟨x, (mem_sdiff.mp (hx.symm ▸ mem_singleton_self x)).2, ?_⟩
  rw [insert_eq, ← hx, sdiff_union_of_subset h'.1]

/-- Reindex extensions by their unique new point. -/
theorem sum_extensions {M : Type*} [AddCommMonoid M] (S : Finset α)
    (f : Finset α → M) :
    ∑ T ∈ extensions S, f T = ∑ x ∈ univ \ S, f (insert x S) := by
  symm
  apply sum_bij (fun x _ => insert x S)
  · intro x hx
    have hx' := (mem_sdiff.mp hx).2
    exact mem_extensions.mpr ⟨subset_insert _ _, card_insert_of_notMem hx'⟩
  · intro x hx y hy he
    have hx' := (mem_sdiff.mp hx).2
    have hy' := (mem_sdiff.mp hy).2
    have : x ∈ insert y S := he ▸ mem_insert_self x S
    exact (mem_insert.mp this).resolve_right hx'
  · intro T hT
    obtain ⟨x, hx, he⟩ := extension_eq_insert hT
    exact ⟨x, by simp [hx], he⟩
  · intro x hx
    rfl

theorem card_extensions (S : Finset α) :
    (extensions S).card = Fintype.card α - S.card := by
  have := sum_extensions S (fun _ => (1 : ℕ))
  simpa [card_sdiff_of_subset (subset_univ S)] using this

/-- The existing degree count on the residual link supplies the full count. -/
theorem extension_sum {B : ι → Finset α} {k : ℕ}
    (hu : Multicover.Uniform B k) (S : Finset α) :
    (∑ T ∈ extensions S, indexedSubsetDegree B T) =
      (k-S.card) * indexedSubsetDegree B S := by
  have h := Multicover.degree_sum_of_uniform (Multicover.subsetLink_uniform hu S)
  have hm (x : {p : α // p ∉ S}) :
      indexedDegree (Multicover.subsetLink B S) x = indexedSubsetDegree B (insert x.val S) := by
    rw [← Multicover.subsetDegree_singleton, Multicover.subsetLink_multiplicity]
    simp [union_singleton]
  simp_rw [hm] at h
  rw [Multicover.subsetLink_card] at h
  rw [sum_extensions]
  have hs : (∑ x : {p : α // p ∉ S}, indexedSubsetDegree B (insert x.val S)) =
      ∑ x ∈ univ \ S, indexedSubsetDegree B (insert x S) := by
    exact (sum_subtype (univ \ S) (by simp) (fun x => indexedSubsetDegree B (insert x S))).symm
  rw [hs] at h
  exact h

/-- Natural excess; the floor lemma below justifies removal of truncation. -/
def excess (B : ι → Finset α) (b : ℕ) (S : Finset α) : ℕ :=
  indexedSubsetDegree B S - b

omit [Fintype α] in
theorem excess_cast {B : ι → Finset α} {b : ℕ} {S : Finset α}
    (hf : b ≤ indexedSubsetDegree B S) :
    (excess B b S : ℤ) = (indexedSubsetDegree B S : ℤ) - b :=
  Nat.cast_sub hf

omit [Fintype α] in
theorem signed_excess_nonneg {B : ι → Finset α} {b : ℕ} {S : Finset α}
    (hf : b ≤ indexedSubsetDegree B S) :
    0 ≤ (indexedSubsetDegree B S : ℤ) - b := by
  rw [← excess_cast hf]
  exact Int.natCast_nonneg _

/-- Exact extension budget, including zero floors and empty occurrences. -/
theorem extension_excess_sum {B : ι → Finset α} {k m n : ℕ}
    (hu : Multicover.Uniform B k) (S : Finset α)
    (hf : m ≤ indexedSubsetDegree B S)
    (hn : ∀ T ∈ extensions S, n ≤ indexedSubsetDegree B T)
    (hb : (k-S.card)*m = (Fintype.card α-S.card)*n) :
    (∑ T ∈ extensions S, excess B n T) = (k-S.card)*excess B m S := by
  have he : (∑ T ∈ extensions S, excess B n T) + (extensions S).card*n =
      (k-S.card)*indexedSubsetDegree B S := by
    rw [← extension_sum hu S]
    have hc : (extensions S).card*n = ∑ T ∈ extensions S, n := by simp
    rw [hc, ← sum_add_distrib]
    apply sum_congr rfl
    intro T hT
    exact Nat.sub_add_cancel (hn T hT)
  rw [card_extensions, ← hb] at he
  have hf' := Nat.sub_add_cancel hf
  change excess B m S + m = indexedSubsetDegree B S at hf'
  nlinarith only [he, congrArg (fun z => (k-S.card)*z) hf']

end CoveringDesigns.LabelledCliques
