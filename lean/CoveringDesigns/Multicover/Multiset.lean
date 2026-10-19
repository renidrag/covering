import CoveringDesigns.Multicover.Schoenheim
import Mathlib.Data.Multiset.Fintype

/-! A thin adapter to Mathlib's multiset occurrence type, retaining every repeat. -/

namespace CoveringDesigns.Multicover

open Finset
universe u
variable {α : Type u} [DecidableEq α]

/-- The occurrence type of `M` is a block together with an index below its count. -/
def ofMultiset (M : Multiset (Finset α)) : M → Finset α := fun i => i

theorem ofMultiset_card (M : Multiset (Finset α)) : Fintype.card M = M.card :=
  Multiset.card_coe M

theorem ofMultiset_subsetDegree (M : Multiset (Finset α)) (X : Finset α) :
    indexedSubsetDegree (ofMultiset M) X = M.countP (X ⊆ ·) := by
  change ((univ : Finset M).val.filter (fun i : M => X ⊆ (i : Finset α))).card = _
  rw [← Multiset.countP_map, Multiset.map_univ_coe]

theorem ofMultiset_degree (M : Multiset (Finset α)) (p : α) :
    indexedDegree (ofMultiset M) p = M.countP (p ∈ ·) := by
  rw [← subsetDegree_singleton, ofMultiset_subsetDegree]
  simp

theorem ofMultiset_uniform (M : Multiset (Finset α)) (k : ℕ) :
    Uniform (ofMultiset M) k ↔ ∀ A ∈ M, A.card = k := by
  constructor
  · intro h A hA
    exact h ⟨A, ⟨0, Multiset.count_pos.mpr hA⟩⟩
  · intro h i
    exact h _ Multiset.coe_mem

theorem ofMultiset_isCover (M : Multiset (Finset α)) (k t lam : ℕ) :
    IsCover (ofMultiset M) k t lam ↔
      (∀ A ∈ M, A.card = k) ∧
      (∀ X : Finset α, X.card = t → lam ≤ M.countP (X ⊆ ·)) := by
  simp only [IsCover, ofMultiset_uniform, Covers, ofMultiset_subsetDegree]

theorem multiset_lower_bound [Fintype α] {M : Multiset (Finset α)} {k t lam : ℕ}
    (htk : t ≤ k) (hkv : k ≤ Fintype.card α)
    (hu : ∀ A ∈ M, A.card = k)
    (hc : ∀ X : Finset α, X.card = t → lam ≤ M.countP (X ⊆ ·)) :
    bound lam (Fintype.card α) k t ≤ M.card := by
  simpa only [ofMultiset_card] using
    lower_bound htk hkv ((ofMultiset_isCover M k t lam).mpr ⟨hu, hc⟩)

end CoveringDesigns.Multicover
