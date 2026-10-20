import CoveringDesigns.SaturatedMatching.CoverFive

/-! Ordinary C(60,31,3)=14 on arbitrary finite point types.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {C : Family α} {p q : α}

theorem no_saturation_31 (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) (hpq : p ≠ q) :
    degree (star C p) q ≠ 2 := by
  intro hs
  obtain ⟨s⟩ := Split.exists_of_saturated (k := 31) (by simpa using hv)
    (by omega) hC hpq hs
  let T := s.matching hv hC hb
  rcases s.matching_card hv hC hb with hfour | hfive
  · exact T.not_four hv hC hb hfour
  · exact T.not_five hv hC hb hfive
end CoveringDesigns.SaturatedMatching

namespace CoveringDesigns.C60_31_3
open Finset SaturatedMatching
variable {α : Type*} [Fintype α]

theorem no_thirteen {C : Family α} (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) : False := by
  classical
  have hp (x y : α) (hxy : x ≠ y) : 3 ≤ degree (star C x) y := by
    have hf := TwoKMinusTwo.pair_ge_two (k := 31) (by simpa using hv) (by omega) hC hxy
    have hn := no_saturation_31 hv hC hb hxy
    omega
  exact no_thirteen_of_pair_floor (fun B : C => B.val) (by simpa using hv)
    (by omega) (by omega) (fun B => hC.1 B.val B.property)
    (fun x y hxy => by simpa only [family_pair] using hp x y hxy)
    (by
      intro U hU
      obtain ⟨A,hA,hUA⟩ := hC.2 U hU
      exact ⟨⟨A,hA⟩,hUA⟩)
    (by simpa using hb)

theorem fourteen_le_card {C : Family α} (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) : 14 ≤ C.card := by
  have hl := TwoKMinusTwoTightening.thirteen_le_card
    (k := 31) (by simpa using hv) (by omega) hC
  by_contra hn
  exact no_thirteen hv hC (by omega)

theorem attaining (hv : Fintype.card α = 60) :
    ∃ C : Family α, IsCover C 31 3 ∧ C.card = 14 := by
  obtain ⟨C,hC,hu⟩ := TwoKMinusTwo.upper_bound (k := 31) (by simpa using hv) (by omega)
  exact ⟨C,hC,Nat.le_antisymm hu (fourteen_le_card hv hC)⟩

theorem exactness_on (hv : Fintype.card α = 60) :
    (∃ C : Family α, IsCover C 31 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C 31 3 → 14 ≤ C.card) :=
  ⟨attaining hv,fun _ hC => fourteen_le_card hv hC⟩
end CoveringDesigns.C60_31_3

namespace CoveringDesigns
theorem covering_number_60_31_3 :
    (∃ C : Family (Fin 60), IsCover C 31 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin 60), IsCover C 31 3 → 14 ≤ C.card) :=
  C60_31_3.exactness_on (by simp)
end CoveringDesigns
