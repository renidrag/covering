import CoveringDesigns.PointReduction.Basic
import CoveringDesigns.Multicover.Links

/-! Universal lower bounds travel upwards in point count; witnesses travel downwards. -/
namespace CoveringDesigns.PointReduction
universe u v w

theorem coverLower_mono {v₀ v₁ k t lam L : ℕ}
    (hk : k ≤ v₀) (hv : v₀ ≤ v₁)
    (hl : Multicover.CoverLower.{u,w} v₀ k t lam L) :
    Multicover.CoverLower.{u,w} v₁ k t lam L := by
  intro α ι _ _ _ B hn hB
  obtain ⟨B', hB'⟩ := reduce_points (β := ULift.{u} (Fin v₀)) hB
    (by simpa using hk) (by simpa [hn] using hv)
  exact hl (by simp) hB'

theorem exists_cover_le {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {k t lam b : ℕ} (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α)
    (h : ∃ B : ι → Finset α, Multicover.IsCover B k t lam ∧ Fintype.card ι ≤ b) :
    ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam ∧ Fintype.card ι ≤ b := by
  obtain ⟨B, hB, hb⟩ := h
  obtain ⟨B', hB'⟩ := reduce_points hB hk hv
  exact ⟨B', hB', hb⟩

/-- An exact supplied occurrence count is retained; this is not a design claim. -/
theorem exists_cover_exact {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {k t lam b : ℕ} (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α)
    (h : ∃ B : ι → Finset α, Multicover.IsCover B k t lam ∧ Fintype.card ι=b) :
    ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam ∧ Fintype.card ι=b := by
  obtain ⟨B, hB, hb⟩ := h
  obtain ⟨B', hB'⟩ := reduce_points hB hk hv
  exact ⟨B', hB', hb⟩

end CoveringDesigns.PointReduction
