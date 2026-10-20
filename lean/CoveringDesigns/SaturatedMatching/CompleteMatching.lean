import CoveringDesigns.SaturatedMatching.CoverPattern

/-! Constructing the complete saturated matching from any one saturated edge.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset TwoKMinusTwo C20_11_3
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {C : Family α} {p q : α}

namespace Split
variable (s : Split C p q 31)

def matchingPoint (z : Option s.crosses × Bool) : α :=
  match z.1 with
  | none => if z.2 then p else q
  | some e => if z.2 then e.val.1 else e.val.2

theorem cross_endpoints (z : s.crosses) :
    z.val.1 ≠ p ∧ z.val.1 ≠ q ∧ z.val.2 ≠ p ∧ z.val.2 ≠ q ∧
      z.val.1 ≠ z.val.2 := by
  obtain ⟨hx,hy⟩ := mem_product.mp (mem_filter.mp z.property).1
  have hn1 := (mem_sdiff.mp hx).2
  have hn2 := (mem_sdiff.mp hy).2
  simp only [mem_insert,mem_singleton,not_or] at hn1 hn2
  exact ⟨hn1.1,hn1.2,hn2.1,hn2.2,fun he =>
    disjoint_left.mp s.geometry.1 hx (he.symm ▸ hy)⟩

theorem matching_endpoints (e : Option s.crosses) :
    s.matchingPoint (e,true) ≠ s.matchingPoint (e,false) := by
  cases e with
  | none => exact s.endpoints
  | some e => exact (s.cross_endpoints e).2.2.2.2

theorem matching_separate (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13)
    (e f : Option s.crosses) (hef : e ≠ f) (b c : Bool) :
    s.matchingPoint (e,b) ≠ s.matchingPoint (f,c) := by
  cases e with
  | none =>
    cases f with
    | none => exact (hef rfl).elim
    | some f =>
      obtain ⟨h1,h2,h3,h4,_⟩ := s.cross_endpoints f
      cases b <;> cases c <;> simp_all [matchingPoint,ne_comm]
  | some e =>
    cases f with
    | none =>
      obtain ⟨h1,h2,h3,h4,_⟩ := s.cross_endpoints e
      cases b <;> cases c <;> simp_all [matchingPoint]
    | some f =>
      have hne : e.val ≠ f.val := by
        intro he; exact hef (congrArg some (Subtype.ext he))
      obtain ⟨⟨h1,h2⟩,h3,h4⟩ := s.cross_disjoint hv hC hb e.property f.property hne
      cases b <;> cases c <;> simp_all [matchingPoint,ne_comm]

theorem matching_injective (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) :
    Function.Injective s.matchingPoint := by
  rintro ⟨e,b⟩ ⟨f,c⟩ he
  by_cases hef : e = f
  · subst f
    have hn := s.matching_endpoints e
    cases b <;> cases c <;> simp_all
  · exact (s.matching_separate hv hC hb e f hef b c he).elim

theorem matching_complete (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13)
    (x y : α) (hxy : x ≠ y) (hsat : degree (star C x) y = 2) :
    ∃ e : Option s.crosses,
      {x,y} = ({s.matchingPoint (e,true),s.matchingPoint (e,false)} : Finset α) := by
  have matep (z : α) (hz : z ≠ p) (hs : degree (star C p) z = 2) : z = q :=
    saturated_matching hv hC hb s.endpoints.symm s.swap.saturated z hz hs
  have mateq (z : α) (hz : z ≠ q) (hs : degree (star C q) z = 2) : z = p :=
    saturated_matching hv hC hb s.endpoints s.saturated z hz hs
  by_cases hxp : x = p
  · subst x
    have hy := matep y hxy.symm hsat
    exact ⟨none,by simp [matchingPoint,hy]⟩
  by_cases hxq : x = q
  · subst x
    have hy := mateq y hxy.symm hsat
    exact ⟨none,by simp [matchingPoint,hy,pair_comm]⟩
  by_cases hyp : y = p
  · subst y
    have hx := matep x hxy (by rwa [pair_degree_comm])
    exact ⟨none,by simp [matchingPoint,hx,pair_comm]⟩
  by_cases hyq : y = q
  · subst y
    have hx := mateq x hxy (by rwa [pair_degree_comm])
    exact ⟨none,by simp [matchingPoint,hx]⟩
  rcases s.separates hv hC hb ⟨hxp,hxq⟩ ⟨hyp,hyq⟩ hxy hsat with h | h
  · have hz : (x,y) ∈ s.crosses := mem_filter.mpr ⟨mem_product.mpr h,hsat⟩
    exact ⟨some ⟨(x,y),hz⟩,rfl⟩
  · have hz : (y,x) ∈ s.crosses :=
      mem_filter.mpr ⟨mem_product.mpr ⟨h.2,h.1⟩,by rwa [pair_degree_comm]⟩
    exact ⟨some ⟨(y,x),hz⟩,by simp [matchingPoint,pair_comm]⟩

noncomputable def matching (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) :
    CoverMatching (M := Option s.crosses) C where
  point := s.matchingPoint
  injective := s.matching_injective hv hC hb
  split e := Classical.choice (by
    cases e with
    | none => exact ⟨s⟩
    | some e =>
      exact exists_of_saturated (by simpa using hv) (by omega) hC
        (s.matching_endpoints (some e)) (mem_filter.mp e.property).2)
  complete := s.matching_complete hv hC hb

theorem matching_card (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) :
    Fintype.card (Option s.crosses) = 4 ∨ Fintype.card (Option s.crosses) = 5 := by
  have hc := (s.small_budget hv hC hb).1
  simp only [Fintype.card_option,Fintype.card_coe]
  omega

end Split
end CoveringDesigns.SaturatedMatching
