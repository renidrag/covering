import CoveringDesigns.Foundations.Links

/-! Elementary lower bounds. These precede, and do not use, GPPT or Stanton. -/

namespace CoveringDesigns

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem one_cover_bound {C : Family α} {k : ℕ} (h : IsCover C k 1) :
    Fintype.card α ≤ k * C.card := by
  have hs : (univ : Finset α) ⊆ C.biUnion id := by
    intro p _
    obtain ⟨B, hB, hp⟩ := h.2 {p} (card_singleton p)
    exact mem_biUnion.mpr ⟨B, hB, hp (mem_singleton_self p)⟩
  have hc := (card_le_card hs).trans card_biUnion_le
  simpa only [card_univ, id_eq, sum_const_nat h.1, Nat.mul_comm] using hc

theorem incidence_lower_bound {C : Family α} {k m : ℕ} (hu : Uniform C k)
    (hl : ∀ p, m ≤ degree C p) :
    m * Fintype.card α ≤ k * C.card := by
  have hs := sum_le_sum (s := (univ : Finset α)) (fun p _ => hl p)
  simpa [degree_sum_of_uniform hu, Nat.mul_comm] using hs

end CoveringDesigns
