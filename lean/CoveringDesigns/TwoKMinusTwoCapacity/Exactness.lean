import CoveringDesigns.TwoKMinusTwoCapacity.Indexed
import CoveringDesigns.TwoKMinusTwo.Bounds
import CoveringDesigns.TwoKMinusTwo.Construction

/-! Ordinary triple-cover exactness from the indexed pair theorem.
The saturation exclusion is used only under its actual small-budget
and parameter hypotheses. The attaining construction is unchanged. -/
namespace CoveringDesigns.TwoKMinusTwoCapacity
open Finset
variable {α : Type*} [Fintype α] {k : ℕ}

private theorem family_pair [DecidableEq α] (C : Family α) (x y : α) :
    indexedSubsetDegree (fun B : C => B.val) {x,y} = degree (star C x) y := by
  classical
  simp only [indexedSubsetDegree, degree, star, card_eq_sum_ones, sum_filter,
    insert_subset_iff, singleton_subset_iff]
  rw [sum_coe_sort C (fun B => if x ∈ B ∧ y ∈ B then (1 : ℕ) else 0)]
  apply sum_congr rfl
  intro B _
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [hx,hy]

/-- Unconditional lower bound on arbitrary finite point labels. -/
theorem fourteen_le_card {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k) (hC : IsCover C k 3) :
    14 ≤ C.card := by
  classical
  by_contra hn
  have hb : C.card ≤ 13 := by omega
  have hp (x y : α) (hxy : x ≠ y) : 3 ≤ degree (star C x) y := by
    have htwo := TwoKMinusTwo.pair_ge_two hv (by omega) hC hxy
    have hne := TwoKMinusTwo.no_saturation_thirteen hv hk hC hb hxy
    omega
  have hi := indexed_fourteen_le_card (fun B : C => B.val) hv hk
    (fun B => hC.1 B.val B.property)
    (by intro x y hxy; simpa only [family_pair] using hp x y hxy)
  apply hn
  simpa only [Fintype.card_coe] using hi

/-- The unchanged upper construction attains fourteen distinct blocks,
because the new lower bound prevents any smaller ordinary image. -/
theorem attaining (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k) :
    ∃ C : Family α, IsCover C k 3 ∧ C.card = 14 := by
  obtain ⟨C,hC,hupper⟩ := TwoKMinusTwo.upper_bound hv (by omega : 3 ≤ k)
  exact ⟨C,hC,Nat.le_antisymm hupper (fourteen_le_card hv hk hC)⟩

/-- Exactness includes both an actual ordinary attaining family and the
universal lower bound; no degree, pair or budget premise remains. -/
theorem exactness (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k) :
    (∃ C : Family α, IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C k 3 → 14 ≤ C.card) :=
  ⟨attaining hv hk, fun _ hC => fourteen_le_card hv hk hC⟩

/-- Conventional `Fin` interface for the stronger family. -/
theorem covering_number (hk : 33 ≤ k) :
    (∃ C : Family (Fin (2*k-2)), IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin (2*k-2)), IsCover C k 3 → 14 ≤ C.card) :=
  exactness (by simp) hk

end CoveringDesigns.TwoKMinusTwoCapacity
