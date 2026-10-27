import CoveringDesigns.C4k_K_2.LowerBound
import CoveringDesigns.C4k_K_2.Attainment
import CoveringDesigns.Foundations.StandardAxioms

/-! Exact values of C(4k,k,2), for every k ≥ 8, on arbitrary finite point types.
Historical geometry and constructions; verified extension/load argument and
formal assembly by Rob Gardiner, with Codex. Publication remains separate. -/
namespace CoveringDesigns.C4k_K_2

/-- Attainment has exactly the required number of DISTINCT blocks. -/
theorem attainment {α : Type*} [Fintype α] {k : ℕ}
    (hk : 8 ≤ k) (hv : Fintype.card α = 4*k) :
    ∃ C : Family α, IsCover C k 2 ∧ C.card = (if 4 ∣ k then 20 else 21) := by
  classical
  obtain ⟨C,hC,hb⟩ := upper_bound hk hv
  exact ⟨C,hC,Nat.le_antisymm hb (lower_bound hk hv hC)⟩

/-- Unconditional arbitrary-label exactness: no supplied geometry or witness premise. -/
theorem exactness {α : Type*} [Fintype α] {k : ℕ}
    (hk : 8 ≤ k) (hv : Fintype.card α = 4*k) :
    (∃ C : Family α, IsCover C k 2 ∧ C.card = (if 4 ∣ k then 20 else 21)) ∧
    (∀ C : Family α, IsCover C k 2 → (if 4 ∣ k then 20 else 21) ≤ C.card) := by
  classical
  exact ⟨attainment hk hv,fun _ hC => lower_bound hk hv hC⟩

theorem covering_number {k : ℕ} (hk : 8 ≤ k) :
    (∃ C : Family (Fin (4*k)), IsCover C k 2 ∧ C.card = (if 4 ∣ k then 20 else 21)) ∧
    (∀ C : Family (Fin (4*k)), IsCover C k 2 → (if 4 ∣ k then 20 else 21) ≤ C.card) :=
  exactness hk (by simp)

#guard_standard_axioms attainment exactness covering_number lower_bound
  indexed_twenty indexed_twenty_one upper_bound

end CoveringDesigns.C4k_K_2
