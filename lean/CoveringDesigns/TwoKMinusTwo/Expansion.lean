import CoveringDesigns.AffineConstructions.Transformations
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators

/-! Nonnegative integer fibre expansion and padding, including empty fibres. -/
namespace CoveringDesigns.TwoKMinusTwo
open Finset

/-- A nonuniform indexed cover with block sizes at most k can be padded,
then deduplicated to an ordinary family. -/
theorem pad_indexed {α ι : Type*} [Fintype α] [Fintype ι]
    (B : ι → Finset α) {k t : ℕ} (hk : k ≤ Fintype.card α)
    (hsize : ∀ i, (B i).card ≤ k)
    (hcover : ∀ T : Finset α, T.card=t → ∃ i, T ⊆ B i) :
    ∃ C : Family α, IsCover C k t ∧ C.card ≤ Fintype.card ι := by
  classical
  have hp (i : ι) : ∃ U : Finset α, B i ⊆ U ∧ U.card=k := by
    obtain ⟨U,hU,_,hc⟩ := exists_subsuperset_card_eq (subset_univ (B i))
      (hsize i) (by simpa using hk)
    exact ⟨U,hU,hc⟩
  choose D hBD hD using hp
  exact AffineConstructions.exists_family_of_blocks D hD (by
    intro T hT
    obtain ⟨i,hi⟩ := hcover T hT
    exact ⟨i,hi.trans (hBD i)⟩)

/-- Weighted expansion of an indexed base cover. Projection may identify
several tested points; fibres of size zero are permitted. -/
theorem weighted_expansion {β ι : Type*} [Fintype β] [Fintype ι]
    (w : β → ℕ) (B : ι → Finset β) {k t : ℕ}
    (hk : k ≤ ∑ x, w x)
    (hsize : ∀ i, (∑ x ∈ B i, w x) ≤ k)
    (hcover : ∀ T : Finset β, T.card ≤ t → ∃ i, T ⊆ B i) :
    ∃ C : Family (Σ x, Fin (w x)), IsCover C k t ∧ C.card ≤ Fintype.card ι := by
  classical
  let E (i : ι) : Finset (Σ x, Fin (w x)) := (B i).sigma (fun _ => univ)
  apply pad_indexed E (by simpa [Fintype.card_sigma] using hk)
  · intro i
    simpa [E, card_sigma] using hsize i
  · intro T hT
    obtain ⟨i,hi⟩ := hcover (T.image Sigma.fst) (card_image_le.trans_eq hT)
    refine ⟨i,?_⟩
    intro x hx
    exact mem_sigma.mpr ⟨hi (mem_image.mpr ⟨x,hx,rfl⟩),mem_univ _⟩

end CoveringDesigns.TwoKMinusTwo
