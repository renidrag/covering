import CoveringDesigns.Multicover.Links

/-! Exact designs on occurrence-indexed blocks. Equal blocks remain separate.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.ExactDesign
open Finset
universe u w
variable {α : Type u} {ι : Type w} [DecidableEq α] [Fintype ι]

/-- Uniform indexed blocks with exactly `lam` occurrences through each t-subset. -/
def IsDesign (B : ι → Finset α) (k t lam : ℕ) : Prop :=
  Multicover.Uniform B k ∧ ∀ X : Finset α, X.card=t → indexedSubsetDegree B X=lam

theorem IsDesign.isCover {B : ι → Finset α} {k t lam : ℕ}
    (h : IsDesign B k t lam) : Multicover.IsCover B k t lam :=
  ⟨h.1, fun X hx => (h.2 X hx).ge⟩

/-- Exact links retain the original occurrence subtype, including strength zero. -/
theorem IsDesign.subsetLink {B : ι → Finset α} {k t lam : ℕ}
    (h : IsDesign B k t lam) (X : Finset α) (hx : X.card ≤ t) :
    IsDesign (Multicover.subsetLink B X) (k-X.card) (t-X.card) lam := by
  refine ⟨Multicover.subsetLink_uniform h.1 X, ?_⟩
  intro T ht
  rw [Multicover.subsetLink_multiplicity]
  apply h.2
  have hd : Disjoint X (T.map (Function.Embedding.subtype _)) := by
    apply disjoint_left.mpr
    intro p hp hpm
    obtain ⟨q, _, rfl⟩ := mem_map.mp hpm
    exact q.property hp
  rw [card_union_of_disjoint hd, card_map, ht, Nat.add_sub_of_le hx]

theorem design_zero_iff (B : ι → Finset α) (k lam : ℕ) :
    IsDesign B k 0 lam ↔ Multicover.Uniform B k ∧ Fintype.card ι=lam := by
  constructor
  · intro h
    exact ⟨h.1, by simpa using h.2 ∅ rfl⟩
  · rintro ⟨hu, hn⟩
    refine ⟨hu, ?_⟩
    intro X hx
    simpa only [card_eq_zero.mp hx, Multicover.subsetDegree_empty] using hn

end CoveringDesigns.ExactDesign
