import CoveringDesigns.Multicover.Schoenheim
import CoveringDesigns.HorsleySingh.SubsetLinks

/-! Compatibility with the unchanged ordinary, distinct-block family interface. -/

namespace CoveringDesigns.Multicover

open Finset
universe u v
variable {α : Type u} [DecidableEq α]

def ofFamily (C : Family α) : C → Finset α := fun A => A.val

omit [DecidableEq α] in
theorem ofFamily_card (C : Family α) : Fintype.card C = C.card := Fintype.card_coe C

theorem ofFamily_subsetDegree (C : Family α) (X : Finset α) :
    indexedSubsetDegree (ofFamily C) X = HorsleySingh.multiplicity C X :=
  (HorsleySingh.multiplicity_eq_indexed C X).symm

theorem ofFamily_degree (C : Family α) (p : α) :
    indexedDegree (ofFamily C) p = CoveringDesigns.degree C p := by
  rw [← subsetDegree_singleton, ofFamily_subsetDegree]
  simp [HorsleySingh.multiplicity, CoveringDesigns.degree, star]

omit [DecidableEq α] in
theorem ofFamily_uniform (C : Family α) (k : ℕ) :
    Uniform (ofFamily C) k ↔ CoveringDesigns.Uniform C k := by
  simp [Uniform, ofFamily, CoveringDesigns.Uniform]

theorem ofFamily_covers_one (C : Family α) (t : ℕ) :
    Covers (ofFamily C) t 1 ↔ CoveringDesigns.Covers C t := by
  rw [covers_one_iff]
  simp [ofFamily, CoveringDesigns.Covers]

theorem ofFamily_isCover_one (C : Family α) (k t : ℕ) :
    IsCover (ofFamily C) k t 1 ↔ CoveringDesigns.IsCover C k t := by
  rw [IsCover, CoveringDesigns.IsCover, ofFamily_uniform, ofFamily_covers_one]

/-- The ordinary bound recovered from the indexed proof, also at strength zero. -/
theorem family_lower_bound [Fintype α] {C : Family α} {k t : ℕ}
    (htk : t ≤ k) (hkv : k ≤ Fintype.card α) (h : CoveringDesigns.IsCover C k t) :
    Schoenheim.bound (Fintype.card α) k t ≤ C.card := by
  simpa only [bound_one_eq, ofFamily_card] using
    lower_bound htk hkv ((ofFamily_isCover_one C k t).mpr h)

variable {ι : Type v} [Fintype ι]

/-- Forget repeated occurrences. Coverage is preserved here only at multiplicity one. -/
def deduplicate (B : ι → Finset α) : Family α := univ.image B

theorem deduplicate_card_le (B : ι → Finset α) :
    (deduplicate B).card ≤ Fintype.card ι := by
  simpa only [deduplicate, card_univ] using card_image_le (s := univ) (f := B)

theorem deduplicate_isCover_one (B : ι → Finset α) (k t : ℕ) :
    CoveringDesigns.IsCover (deduplicate B) k t ↔ IsCover B k t 1 := by
  rw [CoveringDesigns.IsCover, IsCover, covers_one_iff]
  simp [CoveringDesigns.Uniform, CoveringDesigns.Covers, Uniform, deduplicate]

end CoveringDesigns.Multicover
