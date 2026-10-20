import CoveringDesigns.SaturatedMatching.Endpoints
import CoveringDesigns.SaturatedMatching.Budget
import CoveringDesigns.TwoKMinusTwoTightening
import CoveringDesigns.TwoKMinusTwo.Construction

/-! Ordinary C(62,32,3)=14 on arbitrary finite labels.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset

theorem family_pair {α : Type*} [DecidableEq α] (C : Family α) (x y : α) :
    indexedSubsetDegree (fun B : C => B.val) {x,y} = degree (star C x) y := by
  classical
  simp only [indexedSubsetDegree, degree, star, card_eq_sum_ones, sum_filter,
    insert_subset_iff, singleton_subset_iff]
  rw [sum_coe_sort C (fun B => if x ∈ B ∧ y ∈ B then (1 : ℕ) else 0)]
  apply sum_congr rfl
  intro B _
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [hx,hy]

end CoveringDesigns.SaturatedMatching

namespace CoveringDesigns.C62_32_3
open Finset SaturatedMatching
variable {α : Type*} [Fintype α]

theorem no_thirteen {C : Family α} (hv : Fintype.card α = 62)
    (hC : IsCover C 32 3) (hb : C.card = 13) : False := by
  classical
  have hp (x y : α) (hxy : x ≠ y) : 3 ≤ degree (star C x) y := by
    have hf := TwoKMinusTwo.pair_ge_two (k := 32) (by simpa using hv) (by omega) hC hxy
    have hn := no_saturation_32 hv hC hb hxy
    omega
  exact no_thirteen_of_pair_floor (fun B : C => B.val) (by simpa using hv)
    (by omega) (by omega) (fun B => hC.1 B.val B.property)
    (fun x y hxy => by simpa only [family_pair] using hp x y hxy)
    (by
      intro U hU
      obtain ⟨A,hA,hUA⟩ := hC.2 U hU
      exact ⟨⟨A,hA⟩,hUA⟩)
    (by simpa using hb)

/-- Ordinary lower bound; the only premises are cardinality and IsCover. -/
theorem fourteen_le_card {C : Family α} (hv : Fintype.card α = 62)
    (hC : IsCover C 32 3) : 14 ≤ C.card := by
  have hl := TwoKMinusTwoTightening.thirteen_le_card
    (k := 32) (by simpa using hv) (by omega) hC
  by_contra hn
  exact no_thirteen hv hC (by omega)

theorem attaining (hv : Fintype.card α = 62) :
    ∃ C : Family α, IsCover C 32 3 ∧ C.card = 14 := by
  obtain ⟨C,hC,hu⟩ := TwoKMinusTwo.upper_bound (k := 32) (by simpa using hv) (by omega)
  exact ⟨C,hC,Nat.le_antisymm hu (fourteen_le_card hv hC)⟩

theorem exactness_on (hv : Fintype.card α = 62) :
    (∃ C : Family α, IsCover C 32 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C 32 3 → 14 ≤ C.card) :=
  ⟨attaining hv,fun _ hC => fourteen_le_card hv hC⟩

end CoveringDesigns.C62_32_3

namespace CoveringDesigns
theorem covering_number_62_32_3 :
    (∃ C : Family (Fin 62), IsCover C 32 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin 62), IsCover C 32 3 → 14 ≤ C.card) :=
  C62_32_3.exactness_on (by simp)
end CoveringDesigns
