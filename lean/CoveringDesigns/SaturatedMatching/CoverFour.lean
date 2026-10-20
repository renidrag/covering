import CoveringDesigns.SaturatedMatching.CoverBudget

/-! The ordinary k=31 four-pair contradiction.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset TwoKMinusTwo C20_11_3
variable {α M : Type*} [Fintype α] [DecidableEq α] [Fintype M] [DecidableEq M]
variable {C : Family α}

namespace Split
variable {p q : α} (s : Split C p q 31)
theorem residual_of_separated {x y : α}
    (hx : x ≠ p ∧ x ≠ q) (hy : y ≠ p ∧ y ≠ q)
    (hsep : x ∈ s.left ↔ y ∉ s.left) :
    (x ∈ s.X ∧ y ∈ s.Y) ∨ (x ∈ s.Y ∧ y ∈ s.X) := by
  have hxc := s.complementary x hx.1 hx.2
  have hyc := s.complementary y hy.1 hy.2
  simp only [X,Y,mem_sdiff,mem_insert,mem_singleton,not_or]
  by_cases hm : x ∈ s.left
  · left; exact ⟨⟨hm,hx⟩,⟨by tauto,hy⟩⟩
  · right; exact ⟨⟨by tauto,hx⟩,⟨by tauto,hy⟩⟩
end Split

namespace CoverMatching
variable (T : CoverMatching (M := M) C)
include T

theorem four_compatibility (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) (hM : Fintype.card M = 4) :
    FourCompatibility (T.pattern hv hC hb) := by
  let P := T.pattern hv hC hb
  refine ⟨hM,by simpa using hb,T.endpoint_degree hv hC hb,?_,?_,?_⟩
  · intro e; exact (family_pair C _ _).trans (T.split e).saturated
  · intro f g hfg b c
    exact T.pair_floor hv hC hb _ g c (T.point_ne hfg b c) (T.point_ne hfg b (!c))
  · intro e f g hef heg hfg b c hc
    have hsep : T.point (f,b) ∈ (T.split e).left ↔
        T.point (g,c) ∉ (T.split e).left := by
      change P.point (f,b) ∈ (P.block (e,true)).val ↔
        P.point (g,c) ∉ (P.block (e,true)).val
      rw [P.matched,P.matched]
      change (b == P.sign e f) ≠ (c == P.sign e g) at hc
      cases hs : P.sign e f <;> cases ht : P.sign e g <;>
        cases b <;> cases c <;> simp_all
    have hr := (T.split e).residual_of_separated
      ⟨T.point_ne (Ne.symm hef) _ _,T.point_ne (Ne.symm hef) _ _⟩
      ⟨T.point_ne (Ne.symm heg) _ _,T.point_ne (Ne.symm heg) _ _⟩ hsep
    have hf := T.pair_floor hv hC hb _ g c (T.point_ne hfg b c) (T.point_ne hfg b (!c))
    change indexedSubsetDegree (fun A : C => A.val) {T.point (f,b),T.point (g,c)} = 3
    rw [family_pair] at hf ⊢
    rcases hr with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact T.cross_exact hv hC hb hM e hx hy hf
    · rw [pair_degree_comm] at hf ⊢
      exact T.cross_exact hv hC hb hM e hy hx hf

theorem supporting_intersection_sixteen (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) (hM : Fintype.card M = 4)
    (e f : M) (hef : e ≠ f) (a b : Bool) :
    ((T.block (e,a)).val ∩ (T.block (f,b)).val).card = 16 := by
  let P := T.pattern hv hC hb
  have ho : T.point (e,true) ∈ (T.block (f,b)).val ↔
      T.point (e,false) ∉ (T.block (f,b)).val := by
    change P.point (e,true) ∈ (P.block (f,b)).val ↔
      P.point (e,false) ∉ (P.block (f,b)).val
    rw [P.matched,P.matched]
    cases hs : P.sign f e <;> cases b <;> simp_all [Ne.symm hef]
  have hh := (T.split e).balanced_intersections hC (T.four_zero hv hC hb hM e).1
    (T.block (f,b)).property ho
  cases a
  · exact hh.2
  · exact hh.1

theorem not_four (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) (hM : Fintype.card M = 4) : False := by
  obtain ⟨e,f,hef,a,b,hsmall⟩ := four_pair_small_intersection (T.pattern hv hC hb)
    (T.four_compatibility hv hC hb hM) (T.pair_floor hv hC hb)
  have hlarge := T.supporting_intersection_sixteen hv hC hb hM e f hef a b
  change ((T.block (e,a)).val ∩ (T.block (f,b)).val).card = 4 at hsmall
  omega

end CoverMatching
end CoveringDesigns.SaturatedMatching
