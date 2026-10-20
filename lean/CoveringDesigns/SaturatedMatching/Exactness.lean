import CoveringDesigns.C60_31_3
import CoveringDesigns.TwoKMinusTwoCapacity.Exactness

/-! Ordinary exactness for C(2k−2,k,3), k≥31. The unchanged indexed
threefold pair-cover theorem retains its k≥33 scope.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.TwoKMinusTwoMatching
variable {α : Type*} [Fintype α] {k : ℕ}

/-- The only hypotheses are the parameter range, point cardinality and
ordinary uniform triple coverage. -/
theorem fourteen_le_card {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 31 ≤ k) (hC : IsCover C k 3) :
    14 ≤ C.card := by
  by_cases h33 : 33 ≤ k
  · exact TwoKMinusTwoCapacity.fourteen_le_card hv h33 hC
  have hcases : k = 31 ∨ k = 32 := by omega
  rcases hcases with rfl | rfl
  · exact C60_31_3.fourteen_le_card (by simpa using hv) hC
  · exact C62_32_3.fourteen_le_card (by simpa using hv) hC

/-- An actual ordinary family of fourteen distinct blocks, on the given
point type, obtained from the unchanged construction and the lower bound. -/
theorem attaining (hv : Fintype.card α = 2*k-2) (hk : 31 ≤ k) :
    ∃ C : Family α, IsCover C k 3 ∧ C.card = 14 := by
  obtain ⟨C,hC,hu⟩ := TwoKMinusTwo.upper_bound hv (by omega : 3 ≤ k)
  exact ⟨C,hC,Nat.le_antisymm hu (fourteen_le_card hv hk hC)⟩

theorem exactness_on (hv : Fintype.card α = 2*k-2) (hk : 31 ≤ k) :
    (∃ C : Family α, IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C k 3 → 14 ≤ C.card) :=
  ⟨attaining hv hk,fun _ hC => fourteen_le_card hv hk hC⟩

theorem covering_number (hk : 31 ≤ k) :
    (∃ C : Family (Fin (2*k-2)), IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin (2*k-2)), IsCover C k 3 → 14 ≤ C.card) :=
  exactness_on (by simp) hk
end CoveringDesigns.TwoKMinusTwoMatching
