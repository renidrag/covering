import CoveringDesigns.Foundations.Intersecting

/-! Indexed coverings. Equal blocks at distinct indices remain distinct occurrences. -/

namespace CoveringDesigns.Multicover

open Finset
universe u v w
variable {α : Type u} {ι : Type v} {κ : Type w}

/-- Each occurrence has the prescribed size. No injectivity is required. -/
def Uniform (B : ι → Finset α) (k : ℕ) : Prop := ∀ i, (B i).card = k

/-- Every subset of the prescribed strength lies in at least `lam` occurrences. -/
def Covers [Fintype ι] [DecidableEq α] (B : ι → Finset α) (t lam : ℕ) : Prop :=
  ∀ X : Finset α, X.card = t → lam ≤ indexedSubsetDegree B X

def IsCover [Fintype ι] [DecidableEq α] (B : ι → Finset α) (k t lam : ℕ) : Prop :=
  Uniform B k ∧ Covers B t lam

variable [Fintype ι] [DecidableEq α]

theorem subsetDegree_eq_card (B : ι → Finset α) (X : Finset α) :
    indexedSubsetDegree B X = Fintype.card {i // X ⊆ B i} := by
  simp [indexedSubsetDegree, Fintype.card_subtype]

@[simp] theorem subsetDegree_empty (B : ι → Finset α) :
    indexedSubsetDegree B ∅ = Fintype.card ι := by
  simp [indexedSubsetDegree]

@[simp] theorem subsetDegree_singleton (B : ι → Finset α) (p : α) :
    indexedSubsetDegree B {p} = indexedDegree B p := by
  simp [indexedSubsetDegree, indexedDegree]

theorem covers_zero_iff (B : ι → Finset α) (lam : ℕ) :
    Covers B 0 lam ↔ lam ≤ Fintype.card ι := by
  constructor
  · intro h
    simpa using h ∅ rfl
  · intro h X hX
    simpa only [card_eq_zero.mp hX, subsetDegree_empty] using h

theorem covers_multiplicity_zero (B : ι → Finset α) (t : ℕ) : Covers B t 0 :=
  fun _ _ => Nat.zero_le _

theorem covers_one_iff (B : ι → Finset α) (t : ℕ) :
    Covers B t 1 ↔ ∀ X : Finset α, X.card = t → ∃ i, X ⊆ B i := by
  simp [Covers, indexedSubsetDegree, Nat.one_le_iff_ne_zero]

theorem reindex_card [Fintype κ] (e : κ ≃ ι) : Fintype.card κ = Fintype.card ι :=
  Fintype.card_congr e

theorem subsetDegree_reindex [Fintype κ] (e : κ ≃ ι) (B : ι → Finset α)
    (X : Finset α) : indexedSubsetDegree (B ∘ e) X = indexedSubsetDegree B X := by
  rw [subsetDegree_eq_card, subsetDegree_eq_card]
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

theorem degree_reindex [Fintype κ] (e : κ ≃ ι) (B : ι → Finset α) (p : α) :
    indexedDegree (B ∘ e) p = indexedDegree B p := by
  simpa only [subsetDegree_singleton] using subsetDegree_reindex e B {p}

omit [Fintype ι] [DecidableEq α] in
theorem uniform_reindex (e : κ ≃ ι) (B : ι → Finset α) (k : ℕ) :
    Uniform (B ∘ e) k ↔ Uniform B k := by
  exact ⟨fun h i => by simpa using h (e.symm i), fun h i => h (e i)⟩

theorem covers_reindex [Fintype κ] (e : κ ≃ ι) (B : ι → Finset α) (t lam : ℕ) :
    Covers (B ∘ e) t lam ↔ Covers B t lam := by
  simp only [Covers, subsetDegree_reindex]

theorem isCover_reindex [Fintype κ] (e : κ ≃ ι) (B : ι → Finset α) (k t lam : ℕ) :
    IsCover (B ∘ e) k t lam ↔ IsCover B k t lam := by
  rw [IsCover, IsCover, uniform_reindex, covers_reindex]

end CoveringDesigns.Multicover
