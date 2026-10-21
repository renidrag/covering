import CoveringDesigns.Foundations.Basic

/-! Packing incidences on actual finite labels, permitting repeated values. -/
namespace CoveringDesigns.IncidencePacking
open Finset
variable {ε ι : Type*} [DecidableEq ε] [DecidableEq ι]

/-- Each edge needs r actual indices and each index supports at most one edge. -/
theorem packing (M : Finset ε) (I : Finset ι) (S : ε → ι → Prop)
    [DecidableRel S] (r : ℕ)
    (hedge : ∀ e ∈ M, (I.filter (S e)).card = r)
    (hindex : ∀ i ∈ I, ∀ e ∈ M, ∀ f ∈ M, S e i → S f i → e = f) :
    r * M.card ≤ I.card := by
  have hcount : (∑ e ∈ M, (I.filter (S e)).card) =
      ∑ i ∈ I, (M.filter (fun e => S e i)).card := by
    simp only [card_eq_sum_ones, sum_filter]
    exact sum_comm
  have hcap : ∀ i ∈ I, (M.filter (fun e => S e i)).card ≤ 1 := by
    intro i hi
    apply card_le_one.mpr
    intro e he f hf
    exact hindex i hi e (mem_filter.mp he).1 f (mem_filter.mp hf).1
      (mem_filter.mp he).2 (mem_filter.mp hf).2
  have hh := sum_le_sum hcap
  rw [← hcount, sum_congr rfl hedge] at hh
  simpa [Nat.mul_comm] using hh

end CoveringDesigns.IncidencePacking
