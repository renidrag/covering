import CoveringDesigns.Foundations.Relabelling
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Prod

/-! Construction transformations for ordinary finite covering families. -/

namespace CoveringDesigns.AffineConstructions

open Finset

/-- Taking the image of indexed blocks yields an ordinary family; repetitions
can only decrease its cardinality. -/
theorem exists_family_of_blocks {α ι : Type*} [Fintype ι]
    (B : ι → Finset α) {k t : ℕ} (hu : ∀ i, (B i).card = k)
    (hc : ∀ T : Finset α, T.card = t → ∃ i, T ⊆ B i) :
    ∃ C : Family α, IsCover C k t ∧ C.card ≤ Fintype.card ι := by
  classical
  refine ⟨univ.image B, ⟨?_, ?_⟩, ?_⟩
  · intro A hA
    obtain ⟨i, _, rfl⟩ := mem_image.mp hA
    exact hu i
  · intro T hT
    obtain ⟨i, hi⟩ := hc T hT
    exact ⟨B i, mem_image.mpr ⟨i, mem_univ i, rfl⟩, hi⟩
  · exact (card_image_le).trans_eq (card_univ)

/-- Extend a smaller set before applying coverage at strength `t`. -/
theorem covers_subset_of_card_le {α : Type*} [Fintype α]
    {C : Family α} {t : ℕ} (hc : Covers C t) (ht : t ≤ Fintype.card α)
    (T : Finset α) (hT : T.card ≤ t) : ∃ A ∈ C, T ⊆ A := by
  obtain ⟨U, hTU, _, hU⟩ := exists_subsuperset_card_eq (subset_univ T) hT
    (by simpa using ht)
  obtain ⟨A, hA, hUA⟩ := hc U hU
  exact ⟨A, hA, hTU.trans hUA⟩

/-- Blow up every point by the same finite fibre. The projection of a tested
set need not have `t` distinct elements. -/
theorem blow_up {α M : Type*} [Fintype α] [Fintype M]
    {C : Family α} {k t : ℕ} (hc : IsCover C k t) (ht : t ≤ Fintype.card α) :
    ∃ D : Family (α × M), IsCover D (k * Fintype.card M) t ∧ D.card ≤ C.card := by
  classical
  obtain ⟨D, hD, hn⟩ := exists_family_of_blocks
    (fun A : C => (A.val ×ˢ (univ : Finset M)))
    (k := k * Fintype.card M) (t := t)
    (fun A => by simp [hc.1 A.val A.property]) (by
      intro T hT
      obtain ⟨A, hA, hTA⟩ := covers_subset_of_card_le hc.2 ht (T.image Prod.fst)
        ((card_image_le).trans_eq hT)
      refine ⟨⟨A, hA⟩, ?_⟩
      intro x hx
      exact mem_product.mpr ⟨hTA (mem_image.mpr ⟨x, hx, rfl⟩), mem_univ x.2⟩)
  exact ⟨D, hD, by simpa using hn⟩

/-- Restrict blocks along an embedding, then pad to their original size.
Different padded blocks are allowed to coincide. -/
theorem reduce_points {α β : Type*} [Fintype α] [Fintype β]
    {C : Family α} {k t : ℕ} (hc : IsCover C k t)
    (hβα : Fintype.card β ≤ Fintype.card α) (hk : k ≤ Fintype.card β) :
    ∃ D : Family β, IsCover D k t ∧ D.card ≤ C.card := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hβα
  let R (A : C) : Finset β := univ.filter (fun x => e x ∈ A.val)
  have hR (A : C) : (R A).card ≤ k := by
    have hs : (R A).image e ⊆ A.val := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hy).2
    calc
      (R A).card = ((R A).image e).card := (card_image_of_injective _ e.injective).symm
      _ ≤ A.val.card := card_le_card hs
      _ = k := hc.1 A.val A.property
  have hp (A : C) : ∃ U : Finset β, R A ⊆ U ∧ U.card = k := by
    obtain ⟨U, hU, _, hcard⟩ := exists_subsuperset_card_eq (subset_univ (R A))
      (hR A) (by simpa using hk)
    exact ⟨U, hU, hcard⟩
  choose B hRB hB using hp
  obtain ⟨D, hD, hn⟩ := exists_family_of_blocks B hB (by
    intro T hT
    obtain ⟨A, hA, hTA⟩ := hc.2 (T.image e)
      (by rwa [card_image_of_injective _ e.injective])
    refine ⟨⟨A, hA⟩, ?_⟩
    intro x hx
    apply hRB ⟨A, hA⟩
    exact mem_filter.mpr ⟨mem_univ x, hTA (mem_image.mpr ⟨x, hx, rfl⟩)⟩)
  exact ⟨D, hD, by simpa using hn⟩

/-- Transport a construction across equal point counts using the established
relabelling equivalence. -/
theorem exists_cover_of_card_eq {α β : Type*} [Fintype α] [Fintype β]
    (h : Fintype.card α = Fintype.card β) {k t H : ℕ}
    (hc : ∃ C : Family α, IsCover C k t ∧ C.card ≤ H) :
    ∃ D : Family β, IsCover D k t ∧ D.card ≤ H := by
  classical
  obtain ⟨C, hC, hn⟩ := hc
  let e := Fintype.equivOfCardEq h
  exact ⟨relabel e C, relabel_isCover e hC, by simpa [relabel_card] using hn⟩

end CoveringDesigns.AffineConstructions
