import CoveringDesigns.TwoKMinusTwoEquality.Bounds
import CoveringDesigns.TwoKMinusTwo.Construction
import CoveringDesigns.Foundations.StandardAxioms

/-! Reviewed equality refinement of the structural triple-covering family.
The old declarations and thresholds are preserved. Historical priority
remains unresolved. Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusTwoEquality

/-- Arbitrary-label attainment and universal lower fourteen for k≥40. -/
theorem exactness {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 40 ≤ k) :
    (∃ C : Family α, IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C k 3 → 14 ≤ C.card) := by
  classical
  obtain ⟨C,hC,hcard⟩ := TwoKMinusTwo.upper_bound hv (by omega : 3 ≤ k)
  exact ⟨⟨C,hC,Nat.le_antisymm hcard (fourteen_le_card hv hk hC)⟩,
    fun _ h => fourteen_le_card hv hk h⟩

/-- The usual numerical exactness interface, still universally quantified. -/
theorem covering_number {k : ℕ} (hk : 40 ≤ k) :
    (∃ C : Family (Fin (2*k-2)), IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin (2*k-2)), IsCover C k 3 → 14 ≤ C.card) :=
  exactness (by simp) hk

/-- At 36 points the endpoint proof supplies an interval, not exactness. -/
theorem interval_36_19_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 36) :
    (∃ C : Family α, IsCover C 19 3 ∧ C.card ≤ 14) ∧
    (∀ C : Family α, IsCover C 19 3 → 13 ≤ C.card) := by
  classical
  exact ⟨TwoKMinusTwo.upper_bound (by omega : Fintype.card α=2*19-2) (by norm_num),
    fun _ h => lower_bound_36_19_3 hv h⟩

/-- The second equality endpoint includes an actual fourteen-block cover. -/
theorem exactness_78_40_3_on {α : Type*} [Fintype α]
    (hv : Fintype.card α = 78) :
    (∃ C : Family α, IsCover C 40 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C 40 3 → 14 ≤ C.card) :=
  exactness (by omega) (by norm_num)

#guard_standard_axioms lower_bound_36_19_3 lower_bound_78_40_3
  thirteen_le_card fourteen_le_card exactness covering_number

end CoveringDesigns.TwoKMinusTwoEquality
