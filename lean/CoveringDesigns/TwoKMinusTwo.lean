import CoveringDesigns.TwoKMinusTwo.Bounds
import CoveringDesigns.TwoKMinusTwo.Construction
import CoveringDesigns.Foundations.StandardAxioms

/-! The ordinary triple-covering family C(2k-2,k,3).
Structural proofs and weighted affine witnesses; historical priority unresolved.
Research and formalisation by Rob Gardiner with AI assistance. -/

namespace CoveringDesigns.TwoKMinusTwo

/-- Exactness includes an actual family attaining fourteen on arbitrary labels. -/
theorem exactness {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 41 ≤ k) :
    (∃ C : Family α, IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C k 3 → 14 ≤ C.card) := by
  classical
  obtain ⟨C,hC,hcard⟩ := upper_bound hv (by omega : 3 ≤ k)
  exact ⟨⟨C,hC,Nat.le_antisymm hcard (fourteen_le_card hv hk hC)⟩,
    fun _ h => fourteen_le_card hv hk h⟩

/-- The usual numerical interface, still universally quantified over k. -/
theorem covering_number {k : ℕ} (hk : 41 ≤ k) :
    (∃ C : Family (Fin (2*k-2)), IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin (2*k-2)), IsCover C k 3 → 14 ≤ C.card) :=
  exactness (by simp) hk

#guard_standard_axioms conditional_rank saturated_capacity lower_inequality
  upper_bound exactness covering_number

end CoveringDesigns.TwoKMinusTwo
