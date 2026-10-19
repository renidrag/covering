import CoveringDesigns.PointReduction.Bounds
import CoveringDesigns.Multicover.Family

/-! Ordinary-family compatibility uses deduplication only at multiplicity one. -/
namespace CoveringDesigns.PointReduction
universe u v

theorem family_reduce_points {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {C : Family α} {k t : ℕ} (h : IsCover C k t)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α) :
    ∃ D : Family β, IsCover D k t ∧ D.card ≤ C.card := by
  obtain ⟨B', hB'⟩ := reduce_points ((Multicover.ofFamily_isCover_one C k t).mpr h) hk hv
  exact ⟨Multicover.deduplicate B', (Multicover.deduplicate_isCover_one B' k t).mpr hB',
    by simpa using Multicover.deduplicate_card_le B'⟩

theorem family_lower_mono {v₀ v₁ k t L : ℕ} (hk : k ≤ v₀) (hv : v₀ ≤ v₁)
    (hl : ∀ {β : Type u} [Fintype β] [DecidableEq β] {D : Family β},
      Fintype.card β=v₀ → IsCover D k t → L ≤ D.card)
    {α : Type u} [Fintype α] [DecidableEq α] {C : Family α}
    (hn : Fintype.card α=v₁) (h : IsCover C k t) : L ≤ C.card := by
  obtain ⟨D, hD, hc⟩ := family_reduce_points (β := ULift.{u} (Fin v₀)) h
    (by simpa using hk) (by simpa [hn] using hv)
  exact (hl (by simp) hD).trans hc

end CoveringDesigns.PointReduction
